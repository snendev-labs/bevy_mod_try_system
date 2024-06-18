use std::{borrow::Cow, marker::PhantomData};

use bevy::{
    ecs::system::{CombinatorSystem, Combine},
    prelude::{IntoSystem, System},
};

/// Invokes [`Not`] with the output of another system.
///
/// See [`common_conditions::not`] for examples.
///
///
pub type TrySystem<A, B, R, E> = CombinatorSystem<TryMarker<R, E>, A, B>;

/// Any system that outputs a Result is a TrySystem.
///
/// Implemented for functions and closures that convert into [`System<Out=Result<R,E>`](System).
///
/// See similar implementations in the Bevy documentation https://github.com/bevyengine/bevy/blob/main/crates/bevy_ecs/src/schedule/condition.rs#L1240.
pub trait TrySystemExt<In, Marker, R, E>: IntoSystem<In, Result<R, E>, Marker>
where
    R: Send + Sync + 'static,
    E: std::fmt::Debug + Send + Sync + 'static,
{
    fn pipe_err<B: IntoSystem<E, R, M>, M>(
        self,
        other: B,
    ) -> TrySystem<Self::System, B::System, R, E> {
        let a = IntoSystem::into_system(self);
        let b = IntoSystem::into_system(other);
        let name = format!("{} (err -> {})", a.name(), b.name());
        CombinatorSystem::new(a, b, Cow::Owned(name))
    }
}

impl<F, In, Marker, R, E> TrySystemExt<In, Marker, R, E> for F
where
    F: IntoSystem<In, Result<R, E>, Marker>,
    R: Send + Sync + 'static,
    E: std::fmt::Debug + Send + Sync + 'static,
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
    E: std::fmt::Debug + Send + Sync + 'static,
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

    fn handle_errors(In(error): In<TestError>, mut errors: ResMut<ErrorBucket>) {
        errors.0.push(error);
    }

    #[test]
    fn run_try_system() {
        let mut world = World::new();
        world.init_resource::<Counter>();
        world.init_resource::<ErrorBucket>();
        let mut schedule = Schedule::default();

        schedule.add_systems(succeed_increment.pipe_err(handle_errors));
        schedule.add_systems(fail_increment.pipe_err(handle_errors));

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

        schedule.add_systems(alternate_increment.pipe_err(handle_errors));

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
        world.insert_resource(Outputs::default());
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
        world.insert_resource(Outputs::default());
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
        world.insert_resource(Outputs::default());
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
}
