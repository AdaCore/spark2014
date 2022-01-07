This program implements a stopwatch, and is an example of how concurrent
progragms are verified in SPARK. A user can push buttons to start, stop and
reset the clock. The clock has a display to show the elapsed time. This example
uses protected objects and tasks.

GNATprove proves all checks on this program, including the safe usage of
concurrency.
