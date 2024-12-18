# AdaCore TCP/IP stack for high-integrity systems

Copyright (C) 2010, AdaCore

Licensed under the GMGPL.

Example driver code is adapted from original LWIP code:
 Copyright (C) 2001, 2002 Swedish Institute of Computer Science.
 Copyright (C) 2001, 2002 Georges Menie
and is licensed under the GNU General Public License.

## Status of this Code

The intention of this code is to provide an example of the application of
SPARK. It is provided as-is.

## Features

AdaCore TCP/IP stack:
  * Targeted to bare-board embedded applications in certifiable systems.
  * Implemented in SPARK (information flow annotations included)

API:
  * Event driven architecture (based on LWIP design)
  * Application interface based on callbacks

Supported protocols:
  * IPv4
  * ARP
  * UDP
  * TCP
  * ICMP

Environment:
  * No requirement for an underlying OS
  * No threads used
  * For threading applications, user must ensure mutual exclusion
  * Support for multiple user supplied link level drivers
    (examples in C included: Linux socket/TAP interface, NE2k)

Limitations:
  * No IP fragmentation

## Supported Targets

This TCP/IP stack can be used either on a PowerPC bare-board system
or on a Linux host as a native process. In the latter case, the TAP
device is used for communication between the stack and the host system.

The PowerPC version can be run on a QEmu virtual system.

## Build Requirements

Building the TCP/IP Stack requires:
  GNAT Pro >= 6.3.1
  GNU Make >= 3.81

Building for PowerPC also requires the ZFP-Support package to be
installed and available to your cross build chain.

## Building

To build the native Linux version:
   make TARGET=native

To build the PowerPC bareboard version:
   make TARGET=powerpc-elf

This builds a complete example application that implements the TCP echo
service on well-known port 7.

In both cases, the resulting executable is build/app/echop.

## Running the Test Application

To start the PowerPC version under qemu:
   make run

To start the native application using a TAP device:
   build/app/echop tap:

To start the native application using a multicast UDP virtual Ethernet:
   build/app/echop mcast:224.0.0.1:3333
(you can change the IP multicast group address and port number as desired)

The IPstack application configures itself as 192.168.0.1/24.

Note that the first two options above involve opening a TAP device on the
host, which may require super-user privileges. The third option can be
executed by a non-privileged user.

To run another OS in QEmu on the virtual Ethernet, use:
```
  qemu -net nic -net socket,mcast=224.0.0.1:3333 -cdrom other_os.iso
```

## SPARK

To run SPARK tools (currently only flow analysis) on the stack, use:
   make spark

## Acknowledgements

Design ideas have been borrowed from the LWIP stack by Pr. Adam Dunkels
of the Swedish Institute of Computer Science, and are gratefully
acknowledged.
