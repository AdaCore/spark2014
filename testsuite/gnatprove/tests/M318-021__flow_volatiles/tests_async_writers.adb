--  =================
--  = Async_Writers =
--  =================
--
--  * Something might, at any time, update the value in this
--    volatile. Writing to it is completely pointless, it is
--    effectively a black hole. (Only with async_readers will
--    it be meaningful to write to such an object.) In a way
--    this means this is an input_only volatile.
--
--  * Having this volatile appear as an output makes no sense,
--    so we only need to consider the case where it is a global
--    input.

package body Tests_Async_Writers
  with Refined_State => (State_With_Async_Writers => (Vol, Vol2, Vol3))
is
   Vol : Integer with Volatile, Async_Writers, Effective_Reads;

   Vol2 : Integer with Volatile, Async_Writers, Effective_Reads;

   Vol3 : Integer with Volatile, Async_Writers;

   ----------------------------------------------------------------------
   --  The following are "correct" contracts and should not raise any
   --  errors.
   ----------------------------------------------------------------------

   procedure P (X, Y : out Integer)
     with Global  => (In_Out => Vol),
          Depends => (X => Vol,
                      Y => Vol,
                      Vol => Vol)
   is
   begin
      X := Vol;
      Y := Vol;
   end P;

   -- This is illegal.  A Volatile object with Async_Writers true cannot appear
   -- in an expression and therefore cannot be the return expression of the
   -- function.  If it was allowed the function would have a side-effect.
   -- This is different to SPARK 2005.

--     function Q return Integer
--       with Global => (Input => Vol)
--     is
--     begin
--        return Vol;
--     end Q;

   -- Rewrite Q as a procedure
   procedure Proc_Q (V_Out : out Integer)
      with Global  => (In_Out => Vol),
           Depends => (V_Out => Vol,
                       Vol => Vol)
   is
   begin
      V_Out := Vol;
   end Proc_Q;

   procedure Test_01 (X, Y : out Integer)
     with Global  => (In_Out => Vol),
          Depends => (X => Vol,
                      Y => Vol,
                      Vol => Vol)
   is
   begin
      P (X, Y);
   end Test_01;

   procedure Test_02 (X, Y : out Integer)
     with Global  => (In_Out => Vol),
          Depends => (X => Vol,
                      Y => Vol,
                      Vol => Vol)
   is
   begin
      Proc_Q (X);
      Proc_Q (Y);
   end Test_02;

   procedure Test_03 (X : out Integer)
      with Global  => (In_Out => Vol),
           Depends => (X => Vol,
                       Vol => Vol)
   is
   begin
      X := 0;
      while X <= 0 loop
         X := Vol;  --  Not stable
      end loop;
   end Test_03;

   procedure Test_04 (X : out Integer)
      with Global  => (In_Out => Vol),
           Depends => (X => Vol,
                       Vol => Vol)
   is
   begin
      X := 0;
      while X <= 0 loop
         Proc_Q (X);  --  Not stable
      end loop;
   end Test_04;

begin
   declare
      X : Integer;
   begin
      X := Vol;  -- vol is initialized due to having an async_writer
   end;
   Vol2 := 18;  --  also not an error
   --  No error about vol3 either
end Tests_Async_Writers;
