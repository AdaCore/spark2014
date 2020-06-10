with AA; use AA;

package A
with SPARK_Mode,
  Abstract_State => Global_AS
is
   function Global_A_Initalized return Boolean;

   type My_Natural is new Natural with
     Relaxed_Initialization;

   procedure initGlobalsA (status : out Natural) with
     Post => (if status = 0 then Global_A_Initalized),
     Global => (Output => (Global_AA, Global_AS));

   procedure UseA (X : in out Natural) with
     Pre => Global_A_Initalized,
     Global => (Input => Global_AS);

private
   Global_A : My_Natural with Part_Of => Global_AS;

   --function Global_A_Initalized return Boolean is (Global_A'Initialized);
end A;
