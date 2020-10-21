pragma Assertion_Policy (Pre => Check);

package Integrity_Proved with
  SPARK_Mode
is
   procedure Seen_One (X : Integer) with
     Pre  => X >= 0 and then   --  AoRTE
             Invariant,        --  invariant checking
     Post => Invariant;        --  invariant checking

   procedure Seen_Two (X, Y : Natural) with
     Pre  => X < Y and then    --  defensive programming
             Invariant,        --  invariant checking
     Post => Invariant;        --  invariant checking

   function Invariant return Boolean;

end Integrity_Proved;
