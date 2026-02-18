use std::error::Error;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let app = salon::new_app();
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    Ok(axum::serve(listener, app).await?)
}
