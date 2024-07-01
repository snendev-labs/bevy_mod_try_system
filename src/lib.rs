#![cfg_attr(docsrs, feature(doc_auto_cfg))]

//! `bevy_mod_try_system` provides an extension trait for bevy systems that output `Result` types
//! which can distinctly pipe Err and Ok values to separate output systems.
//!
//! This is achieved via the `system.pipe_err(err_system)` method, which passes `Err` variants as
//! input to the `err_system` system, and passes `Ok` variants to subsequent `pipe` calls.
//!
//! In particular, this is useful for managing application-level error context. Since the most
//! common (at least to start) error handling technique might be "log the error", a utility `log_err`
//! for calling `bevy::log::error!` on on any `Err` results is also provided.
//!
//! ## Example
//!
//! In this example, we add an error to a bucket every other update.
//!
//! ```
//! #[derive(Debug)]
//! struct TestError;
//!
//! #[derive(Default, Resource)]
//! struct Bucket(Vec<TestError>);
//!
//! fn increment_and_error_if_even(mut counter: Local<usize>) -> Result<(), TestError> {
//!     *counter += 1;
//!     if *counter % 2 == 1 {
//!         Ok(())
//!     } else {
//!         Err(TestError)
//!     }
//! }
//!
//! fn handle_error(In(error): In<TestError>) {
//!     // todo: do something with the error
//! }
//!
//! fn run_try_system() {
//!     let mut app = App::new();
//!     app.init_resource::<Bucket>();
//!     app.add_systems(increment_and_error_if_even.pipe_err(handle_error));
//!     assert_eq!(world.resource::<Bucket>().0.len(), 0);
//!     app.update();
//!     assert_eq!(world.resource::<Bucket>().0.len(), 0);
//!     app.update();
//!     assert_eq!(world.resource::<Bucket>().0.len(), 1);
//!     app.update();
//!     assert_eq!(world.resource::<Bucket>().0.len(), 1);
//! }
//! ```
//!
//! Consider using or referencing `bevy_anyhow_alerts` to see how to extend this to manage
//! system- and application-level errors.

use std::{borrow::Cow, marker::PhantomData};

use bevy::{
    ecs::system::{AdapterSystem, CombinatorSystem, Combine},
    prelude::{IntoSystem, System},
};

/// A CombinatorSystem for systems that return Results and handle errors.
pub type TrySystem<A, B, R, E> = CombinatorSystem<TryMarker<R, E>, A, B>;

/// An AdapterSystem for systems that return Results and want to log errors.
pub type LogErrorsSystem<S, In, Out, Err, Marker> =
    AdapterSystem<fn(Result<Out, Err>), <S as IntoSystem<In, Result<Out, Err>, Marker>>::System>;

/// Any system that outputs a Result is a TrySystem.
///
/// Implemented for functions and closures that convert into [`System<Out=Result<R,E>`](System).
///
/// See similar implementations in the Bevy documentation https://github.com/bevyengine/bevy/blob/main/crates/bevy_ecs/src/schedule/condition.rs#L1240.
pub trait TrySystemExt<In, Out, Err, M1>
where
    Out: Send + Sync + 'static,
    Err: Send + Sync + 'static,
{
    fn pipe_err<ErrSys, M2>(
        self,
        other: ErrSys,
    ) -> TrySystem<Self::System, ErrSys::System, Out, Err>
    where
        Self: IntoSystem<In, Result<Out, Err>, M1>,
        ErrSys: IntoSystem<Err, Out, M2>,
    {
        let a = IntoSystem::into_system(self);
        let b = IntoSystem::into_system(other);
        let name = format!("{} (err -> {})", a.name(), b.name());
        CombinatorSystem::new(a, b, Cow::Owned(name))
    }

    fn log_err(self) -> LogErrorsSystem<Self, In, Out, Err, M1>
    where
        Self: IntoSystem<In, Result<Out, Err>, M1>,
        Err: std::fmt::Debug,
    {
        self.map(log_error as fn(Result<Out, Err>))
    }
}

fn log_error<R, E: std::fmt::Debug>(result: Result<R, E>) {
    if let Err(error) = result {
        bevy::log::error!("{error:?}");
    }
}

impl<F, In, Out, Err, Marker> TrySystemExt<In, Out, Err, Marker> for F
where
    F: IntoSystem<In, Result<Out, Err>, Marker>,
    Out: Send + Sync + 'static,
    Err: Send + Sync + 'static,
{
}

/// Used with [`CombinatorSystem`] to process systems that output Result types via TrySystemExt.
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct TryMarker<R, E> {
    marker_ok: PhantomData<R>,
    marker_error: PhantomData<E>,
}

impl<R, E> Default for TryMarker<R, E> {
    fn default() -> Self {
        Self {
            marker_ok: PhantomData::<R>,
            marker_error: PhantomData::<E>,
        }
    }
}

impl<A, B, R, E> Combine<A, B> for TryMarker<R, E>
where
    A: System<Out = Result<R, E>>,
    B: System<In = E, Out = R>,
    R: Send + Sync + 'static,
    E: Send + Sync + 'static,
{
    type In = A::In;
    type Out = R;

    fn combine(
        input: Self::In,
        a: impl FnOnce(<A as System>::In) -> <A as System>::Out,
        b: impl FnOnce(<B as System>::In) -> <B as System>::Out,
    ) -> Self::Out {
        a(input).unwrap_or_else(b)
    }
}

#[cfg(test)]
mod tests {
    use bevy::ecs::prelude::*;

    use super::*;

    #[derive(Resource, Default)]
    struct Counter(usize);

    #[derive(Debug)]
    struct TestError;

    #[derive(Default, Resource)]
    struct ErrorBucket(Vec<TestError>);

    type TestResult = Result<(), TestError>;

    fn succeed_increment(mut counter: ResMut<Counter>) -> TestResult {
        counter.0 += 1;
        Ok(())
    }

    fn fail_increment() -> TestResult {
        Err(TestError)
    }

    fn alternate_increment(mut counter: ResMut<Counter>) -> TestResult {
        counter.0 += 1;
        if counter.0 % 2 == 1 {
            Ok(())
        } else {
            Err(TestError)
        }
    }

    fn handle_error(In(error): In<TestError>, mut errors: ResMut<ErrorBucket>) {
        errors.0.push(error);
    }

    #[test]
    fn run_try_system() {
        let mut world = World::new();
        world.init_resource::<Counter>();
        world.init_resource::<ErrorBucket>();
        let mut schedule = Schedule::default();

        schedule.add_systems(succeed_increment.pipe_err(handle_error));
        schedule.add_systems(fail_increment.pipe_err(handle_error));

        schedule.run(&mut world);
        assert_eq!(world.resource::<Counter>().0, 1);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 1);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Counter>().0, 2);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 2);
    }

    #[test]
    fn run_more_try_systems() {
        let mut world = World::new();
        world.init_resource::<Counter>();
        world.init_resource::<ErrorBucket>();
        let mut schedule = Schedule::default();

        schedule.add_systems(alternate_increment.pipe_err(handle_error));

        schedule.run(&mut world);
        assert_eq!(world.resource::<Counter>().0, 1);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 0);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Counter>().0, 2);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 1);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Counter>().0, 3);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 1);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Counter>().0, 4);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 2);
    }

    #[derive(Debug, PartialEq, Eq)]
    enum Output {
        Regular,
        Fallback1,
        Fallback2,
    }

    type TestOutputResult = Result<Output, TestError>;

    fn alternate_output(mut counter: Local<usize>) -> TestOutputResult {
        *counter += 1;
        if *counter % 2 == 1 {
            Ok(Output::Regular)
        } else {
            Err(TestError)
        }
    }

    fn make_fallback_output<E: std::fmt::Debug>(In(error): In<E>) -> Output {
        bevy::log::error!("{error:?}");
        Output::Fallback1
    }

    #[derive(Default, Resource)]
    struct Outputs(Vec<Output>);

    fn collect_output(In(output): In<Output>, mut outputs: ResMut<Outputs>) {
        outputs.0.push(output);
    }

    // Test that pipe_err preserves out types and can be piped from
    #[test]
    fn run_try_and_pipe_systems() {
        let mut world = World::new();
        world.init_resource::<Outputs>();
        let mut schedule = Schedule::default();

        schedule.add_systems(
            alternate_output
                .pipe_err(make_fallback_output)
                .pipe(collect_output),
        );

        assert_eq!(world.resource::<Outputs>().0, vec![]);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Outputs>().0, vec![Output::Regular]);
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Fallback1]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Fallback1, Output::Regular]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![
                Output::Regular,
                Output::Fallback1,
                Output::Regular,
                Output::Fallback1
            ]
        );
    }

    fn make_fallback_string(In(error): In<String>) -> Output {
        bevy::log::error!("{error:?}");
        Output::Fallback1
    }

    // Test that mapping before piping into the system also works
    #[test]
    fn run_map_and_pipe_systems() {
        let mut world = World::new();
        world.init_resource::<Outputs>();
        let mut schedule = Schedule::default();

        schedule.add_systems(
            alternate_output
                .map(|result| result.map_err(|err| format!("{err:?}")))
                .pipe_err(make_fallback_string)
                .pipe(collect_output),
        );

        assert_eq!(world.resource::<Outputs>().0, vec![]);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Outputs>().0, vec![Output::Regular]);
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Fallback1]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Fallback1, Output::Regular]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![
                Output::Regular,
                Output::Fallback1,
                Output::Regular,
                Output::Fallback1
            ]
        );
    }

    #[derive(Debug)]
    struct OtherTestError;
    type NestedTestResult = Result<TestOutputResult, OtherTestError>;

    fn nested_increment(mut counter: Local<Counter>) -> NestedTestResult {
        counter.0 += 1;
        match (counter.0 - 1) % 3 {
            0 => Ok(Ok(Output::Regular)),
            1 => Ok(Err(TestError)),
            2 => Err(OtherTestError),
            _ => unreachable!(""),
        }
    }

    fn make_fallback_result<E: std::fmt::Debug>(In(error): In<E>) -> TestOutputResult {
        bevy::log::error!("{error:?}");
        Ok(Output::Fallback2)
    }

    #[test]
    fn run_pipe_nested_results() {
        let mut world = World::new();
        world.init_resource::<Outputs>();
        let mut schedule = Schedule::default();

        schedule.add_systems(
            nested_increment
                .pipe_err(make_fallback_result)
                .pipe_err(make_fallback_output)
                .pipe(collect_output),
        );

        assert_eq!(world.resource::<Outputs>().0, vec![]);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Outputs>().0, vec![Output::Regular]);
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Fallback1]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Fallback1, Output::Fallback2]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![
                Output::Regular,
                Output::Fallback1,
                Output::Fallback2,
                Output::Regular,
            ]
        );
    }

    fn make_fallback_option<E: std::fmt::Debug, T>(In(error): In<E>) -> Option<T> {
        bevy::log::error!("{error:?}");
        None
    }

    fn collect_options(In(output): In<Option<Output>>, mut outputs: ResMut<Outputs>) {
        if output.is_some() {
            outputs.0.push(output.unwrap());
        }
    }

    #[test]
    fn run_try_and_map_and_pipe_systems() {
        let mut world = World::new();
        world.insert_resource(Outputs::default());
        let mut schedule = Schedule::default();

        schedule.add_systems(
            alternate_output
                .map(|result| result.map(|val| Some(val)))
                .pipe_err(make_fallback_option)
                .pipe(collect_options),
        );

        assert_eq!(world.resource::<Outputs>().0, vec![]);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Outputs>().0, vec![Output::Regular]);
        schedule.run(&mut world);
        assert_eq!(world.resource::<Outputs>().0, vec![Output::Regular]);
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Regular]
        );
        schedule.run(&mut world);
        assert_eq!(
            world.resource::<Outputs>().0,
            vec![Output::Regular, Output::Regular,]
        );
    }

    #[derive(Clone, Debug, PartialEq, Eq, Hash, SystemSet)]
    struct MySystems;

    #[test]
    fn run_pipe_err_and_in_set() {
        let mut world = World::new();
        world.init_resource::<ErrorBucket>();
        let mut schedule = Schedule::default();

        schedule.add_systems(
            || -> TestResult { Ok(()) }
                .pipe_err(handle_error)
                .in_set(MySystems),
        );

        assert_eq!(world.resource::<ErrorBucket>().0.len(), 0);
        schedule.run(&mut world);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 0);
    }

    fn alternate_output_error_vecs(mut counter: Local<usize>) -> Result<(), Vec<TestError>> {
        *counter += 1;
        if *counter % 2 == 1 {
            Ok(())
        } else {
            Err(vec![TestError, TestError])
        }
    }

    fn handle_errors(In(error): In<Vec<TestError>>, mut errors: ResMut<ErrorBucket>) {
        errors.0.extend(error);
    }

    // Test that pipe_err preserves out types and can be piped from
    #[test]
    fn run_pipe_multiple_errors() {
        let mut world = World::new();
        world.init_resource::<ErrorBucket>();
        let mut schedule = Schedule::default();

        schedule.add_systems(alternate_output_error_vecs.pipe_err(handle_errors));

        assert_eq!(world.resource::<ErrorBucket>().0.len(), 0);
        schedule.run(&mut world);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 0);
        schedule.run(&mut world);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 2);
        schedule.run(&mut world);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 2);
        schedule.run(&mut world);
        assert_eq!(world.resource::<ErrorBucket>().0.len(), 4);
    }

    fn _log_err_compiles() {
        let mut schedule = Schedule::default();

        schedule.add_systems(|| -> TestResult { Ok(()) }.log_err().in_set(MySystems));
    }
}
