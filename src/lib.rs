use chrono::{DateTime, DurationRound, TimeDelta, Utc};
use std::cmp::max;
use std::error::Error;
use std::sync::{Arc, RwLock};

const TIME_STEP: TimeDelta = TimeDelta::minutes(15);

/// A time slot.
/// Used to represent an appointment, a shift, some employee availability, etc.
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
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
    // The per-employee lock allows booking Alice without blocking reading Bob's schedule.
    pub employees: Vec<Arc<RwLock<Employee>>>,
}

impl Salon {
    /// Returns a flattened list of all time ranges within query_range where at least one employee
    /// is free.
    //
    // TODO: optimize with Boolean Interval Subtraction using the Sweep-Line algorithm instead of
    // iterative range subtractions.
    pub fn get_available_slots(&self, query_range: TimeRange) -> Vec<TimeRange> {
        let mut all_free_slots = Vec::new();

        for employee_lock in &self.employees {
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

        merge_overlapping_ranges(all_free_slots)
    }

    /// Books an appointment with the given employee if range is still available.
    pub fn book_appointment(
        &self,
        employee_idx: usize,
        time_range: TimeRange,
        phone_num: &str,
    ) -> Result<(), String> {
        let employee_lock = self
            .employees
            .get(employee_idx)
            .ok_or(format!("employee index {employee_idx} not found"))?;

        let mut employee = employee_lock.write().map_err(|e| e.to_string())?;

        if employee.can_book(&time_range) {
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
#[derive(Debug)]
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
    /// Constructs an Employee from a name and list of work shifts.
    pub fn new(name: String, shifts: Vec<TimeRange>) -> Self {
        Self {
            name,
            shifts,
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

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::{TimeZone, Utc};

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
}
