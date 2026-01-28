use chrono::{DateTime, DurationRound, TimeDelta, Utc};
use serde::{Deserialize, Serialize};
use std::cmp::max;
use std::error::Error;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, Write};
use std::path::Path;
use std::sync::{Arc, Mutex, RwLock};

const TIME_STEP: TimeDelta = TimeDelta::minutes(15);

/// A time slot.
/// Used to represent an appointment, a shift, some employee availability, etc.
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Serialize, Deserialize)]
pub struct TimeRange(DateTime<Utc>, DateTime<Utc>);

impl TimeRange {
    /// Constructs a TimeRange from start and end times.
    pub fn new(start: DateTime<Utc>, end: DateTime<Utc>) -> Result<Self, Box<dyn Error>> {
        let dur = end - start;
        if dur < TimeDelta::zero() {
            Err("start date is later than end date")?
        } else {
            Self::from_duration(start, dur)
        }
    }

    /// Constructs a TimeRange from a start time and a duration.
    pub fn from_duration(start: DateTime<Utc>, dur: TimeDelta) -> Result<Self, Box<dyn Error>> {
        let start = start.duration_round_up(TIME_STEP)?;

        let dur = dur.abs();
        let end = start
            .checked_add_signed(dur)
            .ok_or(format!("end date out of range while adding {dur}"))?;

        Ok(Self(start, end))
    }

    fn overlaps(&self, other: &TimeRange) -> bool {
        self.0 < other.1 && self.1 > other.0
    }
}

/// The salon and all its employees.
#[derive(Debug)]
pub struct Salon {
    pub persistence: Arc<PersistenceManager>,
    // The roster (outer) lock allows adding and removing employees to/from the list.
    // The per-employee (inner) lock allows booking Alice without blocking reading Bob's schedule.
    pub employees: RwLock<Vec<Arc<RwLock<Employee>>>>,
}

impl Salon {
    /// Initializes a Salon with data recovered from disk.
    pub fn init<P: AsRef<Path>>(log_path: P) -> Self {
        let mut employees = Vec::new();

        if let Ok(file) = File::open(&log_path) {
            let reader = std::io::BufReader::new(file);
            for l in reader.lines().map_while(Result::ok) {
                if let Ok(action) = serde_json::from_str::<Action>(&l) {
                    Self::apply_action_to_state(&mut employees, action)
                        .expect("failed to apply action to state");
                }
            }
            for employee_lock in &employees {
                let mut employee = employee_lock.write().unwrap();
                employee.shifts = merge_overlapping_ranges(employee.shifts.clone());
            }
        }

        Self {
            persistence: Arc::new(PersistenceManager::new(log_path)),
            employees: RwLock::new(employees),
        }
    }

    /// Modifies the state during recovery without triggering new log writes.
    fn apply_action_to_state(
        state: &mut Vec<Arc<RwLock<Employee>>>,
        action: Action,
    ) -> Result<(), String> {
        match action {
            Action::BookAppointment {
                employee_idx,
                phone_num,
                time_range,
            } => {
                if let Some(employee_lock) = state.get(employee_idx) {
                    let mut employee = employee_lock.write().map_err(|e| e.to_string())?;
                    employee.appointments.push(Appointment {
                        phone_num,
                        time_range,
                    });
                    employee.appointments.sort_by_key(|appt| appt.time_range);
                }
            }
            Action::AddEmployee { name } => {
                state.push(Arc::new(RwLock::new(Employee::new(name))));
            }
            Action::AddShift {
                employee_idx,
                time_range,
            } => {
                if let Some(employee_lock) = state.get(employee_idx) {
                    employee_lock
                        .write()
                        .map_err(|e| e.to_string())?
                        .shifts
                        .push(time_range);
                }
            }
            Action::DelShift {
                employee_idx,
                time_range,
            } => {
                if let Some(employee_lock) = state.get(employee_idx) {
                    let mut employee = employee_lock.write().map_err(|e| e.to_string())?;
                    employee.shifts = subtract_range(employee.shifts.clone(), time_range);
                }
            }
        }
        Ok(())
    }

    /// Returns a flattened list of all time ranges within query_range where at least one employee
    /// is free.
    //
    // TODO: optimize with Boolean Interval Subtraction using the Sweep-Line algorithm instead of
    // iterative range subtractions.
    pub fn get_available_slots(&self, query_range: TimeRange) -> Result<Vec<TimeRange>, String> {
        let mut all_free_slots = Vec::new();

        let employees = self.employees.read().map_err(|e| e.to_string())?;

        for employee_lock in employees.iter() {
            if let Ok(employee) = employee_lock.read() {
                let mut free_slots = employee.shifts.clone();
                for appt in &employee.appointments {
                    free_slots = subtract_range(free_slots, appt.time_range);
                }
                all_free_slots.extend(
                    free_slots
                        .into_iter()
                        .filter(|slot| slot.overlaps(&query_range)),
                );
            }
        }

        Ok(merge_overlapping_ranges(all_free_slots))
    }

    /// Books an appointment with the given employee if range is still available.
    pub fn book_appointment(
        &self,
        employee_idx: usize,
        time_range: TimeRange,
        phone_num: &str,
    ) -> Result<(), String> {
        let employee_lock = {
            let employees = self.employees.read().map_err(|e| e.to_string())?;
            let employee_lock = employees
                .get(employee_idx)
                .ok_or(format!("employee index {employee_idx} not found"))?;
            employee_lock.clone()
        };

        let mut employee = employee_lock.write().map_err(|e| e.to_string())?;

        if employee.can_book(&time_range) {
            self.persistence.log_action(Action::BookAppointment {
                employee_idx,
                phone_num: phone_num.to_string(),
                time_range,
            });

            employee.appointments.push(Appointment {
                phone_num: phone_num.to_string(),
                time_range,
            });
            employee.appointments.sort_by_key(|appt| appt.time_range);

            Ok(())
        } else {
            Err(format!("slot unavailable {time_range:?}"))?
        }
    }

    /// Adds an employee to the roster.
    pub fn add_employee(&self, name: &str) -> Result<(), String> {
        let mut employees = self.employees.write().map_err(|e| e.to_string())?;

        self.persistence.log_action(Action::AddEmployee {
            name: name.to_string(),
        });

        employees.push(Arc::new(RwLock::new(Employee::new(name.to_string()))));

        Ok(())
    }

    /// Extends an employee's work shifts with the given time range.
    pub fn add_shift(&self, employee_idx: usize, time_range: TimeRange) -> Result<(), String> {
        let employee_lock = {
            let employees = self.employees.read().map_err(|e| e.to_string())?;
            let employee_lock = employees
                .get(employee_idx)
                .ok_or(format!("employee index {employee_idx} not found"))?;
            employee_lock.clone()
        };

        let mut employee = employee_lock.write().map_err(|e| e.to_string())?;

        self.persistence.log_action(Action::AddShift {
            employee_idx,
            time_range,
        });

        let mut shifts = employee.shifts.clone();
        shifts.push(time_range);
        employee.shifts = merge_overlapping_ranges(shifts);

        Ok(())
    }

    /// Deducts the given time range from an employee's work shifts.
    /// Appointments that it may no longer be possible to fulfil as a result of this deletion are
    /// intentionally not deleted. The responsibility of reconciling such situation is left to the
    /// caller.
    pub fn del_shift(&self, employee_idx: usize, time_range: TimeRange) -> Result<(), String> {
        let employee_lock = {
            let employees = self.employees.read().map_err(|e| e.to_string())?;
            let employee_lock = employees
                .get(employee_idx)
                .ok_or(format!("employee index {employee_idx} not found"))?;
            employee_lock.clone()
        };

        let mut employee = employee_lock.write().map_err(|e| e.to_string())?;

        self.persistence.log_action(Action::DelShift {
            employee_idx,
            time_range,
        });

        employee.shifts = subtract_range(employee.shifts.clone(), time_range);

        Ok(())
    }
}

// Subtracts a time slot from a list of time slots, potentially splitting a slot in 2.
fn subtract_range(initial_slots: Vec<TimeRange>, sub_slot: TimeRange) -> Vec<TimeRange> {
    let mut result = Vec::new();
    for slot in initial_slots {
        if !slot.overlaps(&sub_slot) {
            result.push(slot);
        } else {
            if slot.0 < sub_slot.0 {
                result.push(TimeRange(slot.0, sub_slot.0));
            }
            if slot.1 > sub_slot.1 {
                result.push(TimeRange(sub_slot.1, slot.1));
            }
        }
    }
    result
}

// Merges overlapping free slots from different employees.
fn merge_overlapping_ranges(mut ranges: Vec<TimeRange>) -> Vec<TimeRange> {
    if ranges.is_empty() {
        return vec![];
    }

    ranges.sort();

    let mut merged = Vec::new();
    let mut current = ranges[0];

    for next in ranges.into_iter().skip(1) {
        if current.1 >= next.0 {
            current.1 = max(current.1, next.1)
        } else {
            merged.push(current);
            current = next;
        }
    }
    merged.push(current);
    merged
}

/// A booked appointment.
/// Associates a time range with relevant metadata that uniquely identifies the person who performed
/// the booking.
#[derive(Debug, PartialEq)]
struct Appointment {
    phone_num: String,
    time_range: TimeRange,
}

/// An employee of the salon.
/// Encapsulates the employee's work shifts and booked appointments.
#[derive(Debug)]
pub struct Employee {
    name: String,
    shifts: Vec<TimeRange>,
    appointments: Vec<Appointment>,
}

impl Employee {
    /// Constructs an Employee from a name.
    pub fn new(name: String) -> Self {
        Self {
            name,
            shifts: Vec::new(),
            appointments: Vec::new(),
        }
    }

    /// Check if range is still available for booking.
    fn can_book(&self, range: &TimeRange) -> bool {
        self.shifts
            .iter()
            .any(|shift| range.0 >= shift.0 && range.1 <= shift.1)
            && !self
                .appointments
                .iter()
                // TODO: optimize conflict detection using Binary Search algorithm.
                .any(|appt| appt.time_range.overlaps(range))
    }
}

/// An action that can be written to a WAL and which the state can be restored from.
#[derive(Serialize, Deserialize, Debug)]
pub enum Action {
    AddEmployee {
        name: String,
    },
    AddShift {
        employee_idx: usize,
        time_range: TimeRange,
    },
    DelShift {
        employee_idx: usize,
        time_range: TimeRange,
    },
    BookAppointment {
        employee_idx: usize,
        phone_num: String,
        time_range: TimeRange,
    },
}

/// Persists writes to a WAL.
#[derive(Debug)]
pub struct PersistenceManager {
    log_file: Mutex<File>,
}

impl PersistenceManager {
    /// Constructs a new PersistenceManager from a file at path.
    pub fn new<P: AsRef<Path>>(path: P) -> Self {
        let file = OpenOptions::new()
            .append(true)
            .create(true)
            .open(path)
            .expect("cannot open WAL file");

        Self {
            log_file: Mutex::new(file),
        }
    }

    /// Appends a command to the log as a single line of JSON.
    pub fn log_action(&self, action: Action) {
        let mut file = self.log_file.lock().unwrap();
        let mut encoded = serde_json::to_string(&action).unwrap();
        encoded.push('\n');
        file.write_all(encoded.as_bytes())
            .expect("WAL write failed");
        file.flush().expect("WAL flush failed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::{TimeZone, Utc};
    use tempfile::NamedTempFile;

    // Creates a DateTime.
    fn t(hour: u32, min: u32) -> DateTime<Utc> {
        Utc.with_ymd_and_hms(2026, 1, 1, hour, min, 0).unwrap()
    }

    // Creates a TimeRange.
    fn range(h1: u32, m1: u32, h2: u32, m2: u32) -> TimeRange {
        TimeRange::new(t(h1, m1), t(h2, m2)).unwrap()
    }

    #[test]
    fn subtract_middle_of_shift() {
        // Scenario: Shift is 09:00 - 12:00. Booking is 10:00 - 11:00.
        // Expect: 09:00-10:00 AND 11:00-12:00
        let shift = vec![range(9, 0, 12, 0)];
        let booking = range(10, 0, 11, 0);

        let result = subtract_range(shift, booking);

        assert_eq!(result.len(), 2);
        assert_eq!(result[0], range(9, 0, 10, 0));
        assert_eq!(result[1], range(11, 0, 12, 0));
    }

    #[test]
    fn subtract_exact_match() {
        // Scenario: Shift is 09:00 - 10:00. Booking is 09:00 - 10:00.
        // Expect: Empty list
        let shift = vec![range(9, 0, 10, 0)];
        let booking = range(9, 0, 10, 0);

        let result = subtract_range(shift, booking);

        assert!(result.is_empty());
    }

    #[test]
    fn subtract_overlap_start() {
        // Scenario: Shift 09:00 - 12:00. Booking 08:00 - 10:00 (starts before shift).
        // Expect: 10:00 - 12:00
        let shift = vec![range(9, 0, 12, 0)];
        let booking = range(8, 0, 10, 0);

        let result = subtract_range(shift, booking);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0], range(10, 0, 12, 0));
    }

    #[test]
    fn merge_simple_overlap() {
        // Alice: 09:00 - 10:00
        // Bob:   09:30 - 10:30
        // Expect: 09:00 - 10:30
        let inputs = vec![range(9, 0, 10, 0), range(9, 30, 10, 30)];
        let result = merge_overlapping_ranges(inputs);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0], range(9, 0, 10, 30));
    }

    #[test]
    fn merge_contiguous_slots() {
        // Alice works morning: 09:00 - 12:00
        // Alice works afternoon: 12:00 - 15:00
        // Expect: 09:00 - 15:00 (Seamless availability)
        let inputs = vec![range(9, 0, 12, 0), range(12, 0, 15, 0)];
        let result = merge_overlapping_ranges(inputs);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0], range(9, 0, 15, 0));
    }

    #[test]
    fn merge_engulfed_slots() {
        // Alice: 09:00 - 17:00 (Full day)
        // Bob:   12:00 - 13:00 (Lunch cover)
        // Expect: 09:00 - 17:00 (Bob adds no *new* availability coverage to the business)
        let inputs = vec![range(9, 0, 17, 0), range(12, 0, 13, 0)];
        let result = merge_overlapping_ranges(inputs);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0], range(9, 0, 17, 0));
    }

    #[test]
    fn merge_disjoint_slots() {
        // Alice: 09:00 - 10:00
        // Bob:   11:00 - 12:00
        // Expect: Two separate ranges
        let inputs = vec![range(9, 0, 10, 0), range(11, 0, 12, 0)];
        let result = merge_overlapping_ranges(inputs);

        assert_eq!(result.len(), 2);
        assert_eq!(result[0], range(9, 0, 10, 0));
        assert_eq!(result[1], range(11, 0, 12, 0));
    }

    #[test]
    fn init_recover_shifts() {
        // Disjointed modifications to an employee's shifts (extend, deduct).
        // Expect: Merged and sorted shifts with empty time ranges in between.
        let mut wal = NamedTempFile::with_prefix("salontest_").unwrap();
        let action_log = "\
            {\"AddEmployee\":{\"name\":\"Alice\"}}\n\
            {\"AddShift\":{\"employee_idx\":0,\"time_range\":[\"2026-01-01T10:00:00Z\",\"2026-01-01T12:00:00Z\"]}}\n\
            {\"DelShift\":{\"employee_idx\":0,\"time_range\":[\"2026-01-01T07:00:00Z\",\"2026-01-01T07:30:00Z\"]}}\n\
            {\"AddShift\":{\"employee_idx\":0,\"time_range\":[\"2026-01-01T08:00:00Z\",\"2026-01-01T10:00:00Z\"]}}\n\
            {\"DelShift\":{\"employee_idx\":0,\"time_range\":[\"2026-01-01T10:00:00Z\",\"2026-01-01T10:30:00Z\"]}}\n\
            {\"DelShift\":{\"employee_idx\":0,\"time_range\":[\"2026-01-01T10:15:00Z\",\"2026-01-01T11:00:00Z\"]}}\n\
            ";
        wal.write_all(action_log.as_bytes()).unwrap();

        let s = Salon::init(wal);

        let employees = s.employees.read().unwrap();
        let employee = employees.first().unwrap().read().unwrap();

        assert_eq!(
            employee.shifts,
            vec![range(8, 0, 10, 0), range(11, 0, 12, 0)]
        );
    }

    #[test]
    fn init_recover_appointments() {
        // Populate various appointments, some valid, some not (unknown employee, overlaps).
        // Expect: Appointments added as-is, but sorted. Validations are the responsibility of the
        // business logic, not the data recovery logic.
        let mut wal = NamedTempFile::with_prefix("salontest_").unwrap();
        let action_log = "\
            {\"AddEmployee\":{\"name\":\"Alice\"}}\n\
            {\"AddEmployee\":{\"name\":\"Bob\"}}\n\
            {\"BookAppointment\":{\"employee_idx\":0,\"phone_num\":\"0001\",\"time_range\":[\"2026-01-01T13:00:00Z\",\"2026-01-01T14:00:00Z\"]}}\n\
            {\"BookAppointment\":{\"employee_idx\":0,\"phone_num\":\"0002\",\"time_range\":[\"2026-01-01T09:00:00Z\",\"2026-01-01T10:30:00Z\"]}}\n\
            {\"BookAppointment\":{\"employee_idx\":1,\"phone_num\":\"0003\",\"time_range\":[\"2026-01-01T09:00:00Z\",\"2026-01-01T10:00:00Z\"]}}\n\
            {\"BookAppointment\":{\"employee_idx\":1,\"phone_num\":\"0004\",\"time_range\":[\"2026-01-01T13:00:00Z\",\"2026-01-01T14:30:00Z\"]}}\n\
            {\"BookAppointment\":{\"employee_idx\":9,\"phone_num\":\"0001\",\"time_range\":[\"2026-01-01T09:00:00Z\",\"2026-01-01T10:30:00Z\"]}}\n\
            {\"BookAppointment\":{\"employee_idx\":1,\"phone_num\":\"0001\",\"time_range\":[\"2026-01-01T09:45:00Z\",\"2026-01-01T10:15:00Z\"]}}\n\
            {\"BookAppointment\":{\"employee_idx\":0,\"phone_num\":\"0001\",\"time_range\":[\"2026-01-01T22:00:00Z\",\"2026-01-01T23:00:00Z\"]}}\n\
            ";
        wal.write_all(action_log.as_bytes()).unwrap();

        let s = Salon::init(wal);

        let employees = s.employees.read().unwrap();
        assert_eq!(employees.len(), 2);

        fn appt(phone_num: &str, time_range: TimeRange) -> Appointment {
            Appointment {
                phone_num: phone_num.to_string(),
                time_range,
            }
        }

        let e1 = employees.first().unwrap().read().unwrap();
        assert_eq!(e1.name, "Alice",);
        assert_eq!(
            e1.appointments,
            vec![
                appt("0002", range(9, 0, 10, 30)),
                appt("0001", range(13, 0, 14, 0)),
                appt("0001", range(22, 0, 23, 0)),
            ]
        );

        let e2 = employees.get(1).unwrap().read().unwrap();
        assert_eq!(e2.name, "Bob",);
        assert_eq!(
            e2.appointments,
            vec![
                appt("0003", range(9, 0, 10, 0)),
                appt("0001", range(9, 45, 10, 15)),
                appt("0004", range(13, 0, 14, 30)),
            ]
        );
    }
}
