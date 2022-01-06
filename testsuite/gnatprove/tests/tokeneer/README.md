This program is a highly secure biometric software system that was originally
developed by Altran. The system provides protection to secure information held
on a network of workstations situated in a physically secure enclave. The
Tokeneer project was commissioned by the US National Security Agency (NSA) to
demonstrate the feasibility of developing systems to the level of rigor
required by the higher assurance levels of the Common Criteria. The
requirements of the system were captured using the Z notation and the
implementation was in SPARK 2005. The original development artifacts, including
all source code, are [publicly
available](http://www.adacore.com/sparkpro/tokeneer).

The program in the toolset distribution is a translation of the original
Tokeneer code into SPARK 2014. The core system now consists of approximately
10,000 lines of SPARK 2014 code. There are also approximately 3,700 lines of
supporting code written in Ada which mimick the drivers to peripherals
connected to the core system.

Data and flow dependency contracts are given for all subprograms. Partial
functional contracts are also given for a subset of subprograms. GNATprove
currently proves automatically all checks on SPARK code in Tokeneer. The
transition from SPARK 2005 to SPARK 2014 was presented in a [post on the AdaCore
Blog](https://blog.adacore.com/tokeneer-fully-verified-with-spark-2014)

Tokeneer can be used as the basis for demonstrating four types of security
vulnerabilities that can be detected by GNATprove, when calling GNAT Studio with
`-XSECURITY_DEMO=True` (or changing the value of the scenario variable in
GNAT Studio). Analyzing the code in that setting detects:

* an information leak in `keystore.adb`
* a back door in `bio.adb`
* a buffer overflow in `admintoken.adb`
* an implementation flaw in `alarm.adb`
