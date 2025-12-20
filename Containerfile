FROM rust:1.92 AS build

WORKDIR app/
COPY . .
RUN cargo build --release


FROM debian:trixie-slim AS app

COPY --from=build /app/target/release/astraea /

ENTRYPOINT ["/astraea"]
