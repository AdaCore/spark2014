This program was originally a case study written in SPARK 2005 by John Barnes,
presented in section 14.3 of his book `"High Integrity Software, The SPARK
Approach to Safety and Security"` (2003) and section 15.1 of the updated book
`"SPARK: The Proven Approach to High Integrity Software"` (2012). For details on
this case study, see one of the above books. The program in the toolset
distribution is the SPARK 2014 version of this case study.

The program considers the control system of an autopilot controlling both
altitude and heading of an aircraft. The altitude is controlled by manipulating
the elevators and the heading is controlled by manipulating the ailerons and
rudder.

The values given by instruments are modelled as External State Abstraction with
asynchronous writers (the sensors) in package `Instruments`. The states of
controllers are modelled as a State Abstraction called `State` in package `AP`,
which is successively refined into finer-grain abstractions in the child
packages of `AP` (for example `AP.Altitude` and `AP.Altitude.Pitch`). The
actions on the mobile surfaces of the plane are modelled as with asynchronous
readers (the actuators) in package `Surfaces`.

Data and flow dependency contracts are given for all subprograms. GNATprove
proves all checks on this program, except for 4 runtime checks related to
scaling quantities using a division (a known limitation of automatic provers).
