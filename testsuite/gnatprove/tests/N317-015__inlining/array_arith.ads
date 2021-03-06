package Array_Arith
  with SPARK_Mode
is

   type Idx is range 1 .. 10;
   type T is array (Idx) of Natural;

   procedure Init (X : out T) with
     Post => (for all J in Idx => X(J) = Natural(J));  -- @POSTCONDITION:PASS

   procedure Init2 (X : out T) with
     Post => (for all J in Idx => X(J) = Natural(J) + 1);  -- @POSTCONDITION:PASS

   procedure Init3 (X : out T) with
     Post => (for all J in Idx => X(J) = Natural(J) + 1);

   procedure Zero (X : out T) with
     Post => (for all J in Idx => X(J) = 0);  -- @POSTCONDITION:PASS

end Array_Arith;
