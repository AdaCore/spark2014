procedure Specialized_Param_In_Iterated
  with
    SPARK_Mode => On
is

   --  We do not support specialized parameters inside iterated component
   --  associations.

   type Nat_Array is array (Positive range <>) of Natural;

   function Init_Array (Last : Integer; Init : not null access function (I : Positive) return Natural) return Nat_Array with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Always_Return),
     Post => Init_Array'Result = (for I in 1 .. Last => Init (I));

   function Init_Array (Last : Integer; Init : not null access function (I : Positive) return Natural) return Nat_Array is
   begin
      return (for I in 1 .. Last => Init (I));
   end Init_Array;

   function Consecutive_Numbers (F : Positive; N : Natural) return Nat_Array with
     Pre  => F - 1 <= Natural'Last - N,
     Post => Consecutive_Numbers'Result = (for I in F .. F - 1 + N => I);

   function Consecutive_Numbers (F : Positive; N : Natural) return Nat_Array is
      function Nth (I : Positive) return Natural is
        (if I <= Natural'Last - F + 1 then F - 1 + I else 0);
   begin
      return Init_Array (N, Nth'Access);
   end Consecutive_Numbers;

begin
   null;
end Specialized_Param_In_Iterated;
