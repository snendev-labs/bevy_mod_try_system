# bevy_mod_try_system

[![Crates.io](https://img.shields.io/crates/v/bevy_mod_try_system.svg)](https://crates.io/crates/bevy_mod_try_system)
[![Docs](https://docs.rs/bevy_mod_try_system/badge.svg)](https://docs.rs/bevy_mod_try_system/latest/)


This crate defines `TrySystemExt`, an extension trait implemented on all `IntoSystem` with `Out = Result<Val, Error>`. It provides a method, `pipe_err`, which accepts `self` and another system (with `In = Error`) as parameters, and returns a `CombinerSystem` (the same vehicle behind `PipeSystem` and the `system.pipe` method) that passes errors from the first system into the second system.

## Warnings about chained outputs.

Assume we intend to call `system_a.pipe_err(system_b)`, where `system_a` returns some type `Result<(), Error>`. If we wanted to pipe some output `Value` from `system_a` out to a third `system_c`, we can, as long as system B can provide fallback values of `Value` when system `A` returns an `Error`:

```rust
fn system_a() -> Result<Value, Error> {
    // ...
}

fn system_b(In(error): In<Error>) -> Value {
    // ...
}

fn system_c(In(value): In<Value>) {
    // ...
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Update, system_a.pipe_err(system_b).pipe(system_c))
        .run();
}
```

Importantly, if `system_b` cannot provide a fallback value, then this doesn't work very well. However, you can usually be clever, for example returning `Option<Value>` from `system_b` and using `system.map`:

```rust
// ...
fn system_b(In(error): In<Error>) -> Value {
    // ...
}

// ...
app.add_systems(Update, system_a.map(|result| result.map(|value| Some(value))).pipe_err(system_b).pipe(system_c));
```

See the tests for more information.
