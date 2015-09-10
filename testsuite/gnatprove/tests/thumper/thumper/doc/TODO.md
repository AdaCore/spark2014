
Thumper TODO
============

There are several general areas where work is needed. The order of the items below is in
approximate priority order. The focus is first on the server (implementation followed by
testing) and then the client. Interaction with a database or with web clients would be fun and
interesting but not essential to the functionality of the system.

+ Hermes ASN.1 Encoding/Decoding Logic.
+ Interfacing to OpenSSL.
+ Testing/Verification.
+ Client Logic.
+ GUI for the Client.
+ Database Connectivity.
+ Web Configurability via AWS.

Here are some more details about each of these areas. For each area I outline briefly what that
area entails (as I see it) along with some issues that need to be solved.

Hermes ASN.1 Encoding/Decoding Logic
------------------------------------

Package Bodies: `Hermes.DER.Decode` & `Hermes.DER.Encode`

Conceptually the communication between client and server is simple: the client sends a request
and the server replies with the time stamp. However, RFC-3161 requires that these messages be
formatted according to ASN.1 rules which are intricate and complex. The handling of ASN.1 is
factored into a separate library (Hermes) due to its applicability to other projects.

This area would entail learning about the ASN.1 formatting rules and providing the necessary
subprograms to encode/decode data according to those rules. This work has already been started
but it is incomplete.

Another aspect of this area is that the ASN.1 encoding/decoding (basically the Hermes library)
should be written in SPARK and proved free of runtime errors. Thus this area would also entail
working more closely with SPARK.

As an aside... The "proper" way to deal with ASN.1 is to use a tool called an "ASN.1 compiler"
that converts the high level notation of a protocol into code in some programming language that
implements the encoding/decoding of that protocol. Once the ASN.1 compiler is written it can be
used for any protocol that employs ASN.1, greatly simplifying the task of using ASN.1 in
applications. It is *not* the intention of this project to go this route. Instead we will hand
build the encoding/decoding subprograms.

There is a group looking at creating an ASN.1 compiler that generates Ada (none currently exists
as far as I know) but they are not planning to output provable SPARK. At some future time the
Hermes effort may wish to become associated with this other effort in some way.

Interfacing to OpenSSL
----------------------

Package Body: `Cryptographic_Services`

In theory Thumper should use a cryptographic library written in SPARK that is proved free of
runtime errors. However no such library is available with the necessary cryptographic primitives
(but my "ACO" project aims to build such a library and could potentially be used with Thumper in
the future). Thus in the interest of practicality Thumper currently uses the widely known
OpenSSL cryptographic library.

OpenSSL is written in C and so this area is mostly about interfacing Ada to C. The method for
doing this is described in AdaCore's documentation for GNAT and in the Ada standard itself. In
principle it isn't hard to do but, as always, the devil is in the details.

The building of Thumper will become more complex due to this mixed language interaction. First
it may be necessary to write some C helper functions (GPS allows projects that are a mixture of
Ada and C so this is not a show stopper). Second it will be necessary to install OpenSSL and
work out how to draw its libraries into the Thumper build.

One extra complication is that a true X.509 certificate will be needed by the OpenSSL functions.
Fortunately the OpenSSL library comes with a program for creating and managing such
certificates. Learning how to use that program is thus also a part of this area.

Testing/Verification
--------------------

Package Bodies: The various `Check_*` packages in the `tests` folders of Thumper and Hermes.

Some software teams designate one team member to the job of testing. In such teams that person
because a "testing specialist" that writes tests for all aspects of the project. That is the
approach I'm visualizing here.

The current code base has a few tests already created but they are minimal. Furthermore as more
functionality is written, it will need to be tested. All tests should be fully automated so they
can be easily executed in batch. In many environments a special server (called a "continuous
integration" server) is configured to build and test the entire system after every commit... or
at least every day. Although I'm not suggesting we go that far we should at least have tests
that could potentially be used in that kind of environment.

Some tests are complicated to do automatically such as tests involving multiple, interacting
programs (client/server!). This area is all about building tests, making sure the tests pass,
and alerting responsible people to tests that are failing.

Because certain parts of Thumper and Hermes are in SPARK, this area should also concern itself
with running the SPARK verification tools over all parts of the system that are supposed to
verify successfully to ensure that they actually do.

Note that some testing might be done via scripts using a currently unspecified scripting
language.

Client Logic
------------

Package Bodies: `Client_SPARK_Boundary` & `Client_Timestamp_Maker`

At the time of this writing the client is very underdeveloped. In contrast the main structure of
the server is in place. This area is about fixing that situation and filling in the client so
that it can function.

Roughly the client needs to somehow accept the name of a file from the user (command line
switch? prompt the user? GUI interface---see below?). Then the client must construct a suitable
request message, send the request to the server, receive the response, and check the response.
The client should be able to share some code with the server and would also make use of Hermes
just as the server does. Thus part of what needs to be done for this area is coordinating with
whoever is finishing the ASN.1 implementation and reusing as much server logic as possible (such
as the network handling packages that already exist).

GUI for the Client
------------------

The Thumper client will be run by ordinary computer users to get time stamps from the Thumper
server. It should thus be as easy to use as possible. A command line interface may be suitable
for experienced users but probably isn't suitable for non-specialists. This area is about adding
a simple GUI interface to the client to improve the user experience.

Roughly the interface would allow the user to select a file (or multiple files?) using the
standard File Open dialog box and then get time stamps for the file (or files) selected. It
should provide the user with some feedback about the process so the user is alerted to errors or
delays.

There are several options for GUI programming in Ada. One possibility is to use GtkAda from
AdaCore. This library is used by, for example, GPS (yes, GPS is written in Ada) so the "look" of
the interface it provides is known to you. There is tutorial information on using GtkAda on
AdaCore's web site and elsewhere on the web. If you are interested in GUI programming you might
find it interesting to see one way of doing it in Ada.

Database Connectivity
---------------------

Package Body: `Data_Storage`

Adding a database to Thumper could be considered an example of over engineering. Also security
sensitive software is usually best served by being simple and databases add complexity. However,
Thumper could potentially make use of a database for storing information about each request it
receives and each time stamp that it makes. Such information could be used to analyze usage
patterns and for auditing purposes.

This area is about setting up a database server (again over engineering!) and a suitable library
for interacting with it. I recommend PostgreSQL for the database server. There are a couple of
options for the library that we could discuss.

The idea would be to add some code to Thumper that constructs appropriate queries and then uses
the library to add or retrieve information from the database. Some database administration (not
much) would also be necessary.


Web Configurability via AWS
---------------------------

Package Body: `Remote_Access`

The Ada Web Server (AWS) is a library that can be added to your application that turns your
application into a web server along with whatever else it is doing. Whenever a client tries to
access a page from your server, a procedure in your application is called to generate the page.
Since that procedure is entirely general, pages can be computed using whatever means are
necessary.

Using AWS with Thumper could be considered another example of over engineering. However, it
might be nice if Thumper had a web interface that allowed an administrator to view statistics
about the server, perhaps drawn from the database, or even configure the server.

This area requires learning about AWS and incorporating it into Thumper so that Thumper can
respond to simple web requests. This also makes use of Ada's multi-tasking features; the
internal web server runs in a separate task.
