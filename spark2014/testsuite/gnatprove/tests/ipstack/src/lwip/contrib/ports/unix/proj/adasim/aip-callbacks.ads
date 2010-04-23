------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Callbacks is

   --  Eventually, callbacks will be identified by integer values and the user
   --  data argument will be an integer index as well, designating a state
   --  array entry.

   --  As long as we rely on the original LWIP implementation, callbacks
   --  are expected to be pointers to subprograms and the user data argument
   --  is passed around as an opaque pointer.

   --  We pass bare subprogram addresses as callback points and pass the
   --  integer values as the user data argument already, using an integer type
   --  sized as an address (AIP.IPTR_T). This is handled the same as a pointer
   --  through LWIP and allows array indexing the way we'll need eventually.

   subtype Callback_Id is AIP.IPTR_T;
   NOCB : constant Callback_Id := AIP.NULIPTR;


   --  LWIP callbacks are often expected to be functions returning values.
   --  They however most often modify pieces of global state (e.g. adjusting a
   --  pbuf), which requires procedures in SPARK.

   --  Our examples use procedures with an out parameter on the SPARK/Ada side
   --  and resort to C wrappers to bridge. These wrappers expect (err_t *)
   --  formals, return err_t values, and call our Spark/Ada callbacks in
   --  between, which we need to export.

   --  Exporting requires a standalone spec, forbidden in SPARK package
   --  bodies, so we group everything (exports and imports) in package
   --  specs. This will all become simpler when we reimplement and are not
   --  constrained by binding requirements any more.

   --  In the current scheme, callback Id's are actually subprogram addresses.
   --  To minimize the SPARK non compliance points, our binding formals use
   --  IPTR for subprogram addresses and we convert from real addresses at
   --  registration points. This is achieved with AIP.Conversions.  The latter
   --  resorts to System.Address, ~impossible to have visibility on in SPARK,
   --  so uses in examples are factorized in hidden suprogram bodies.

end AIP.Callbacks;
