package body Justifinit
  with SPARK_Mode,
       Refined_State => (State => X)
is
   X : Integer;

   procedure P (Y : in out Integer) is
   begin
      null;
   end P;

   procedure Q (Y : in out Integer)
     with Global => (Input => X)
   is
   begin
      null;
   end Q;
end Justifinit;
