pragma Extensions_Allowed (All_Extensions);

procedure Folded_Inputs
  (P_In    :     Boolean;
   P_Index :     Positive;
   P_Proof :     Integer;
   P_Out   : out Boolean)
with
  SPARK_Mode,
  Pre => P_Index in 1 .. 2 and then P_Proof > 0
is
   type Value_Array is array (1 .. 2) of Boolean;

   function Pick (Value : Positive; Checked : Integer) return Positive
   with
     Global  => (Proof_In => P_Proof),
     Pre     => P_Proof > 0,
     Depends => (Pick'Result => Value, null => Checked);

   function Pick (Value : Positive; Checked : Integer) return Positive is
     (Value);

   Values        : Value_Array := (others => P_In);
   Uninitialized : Integer;
begin
   --  The indexed component is an otherwise-supported object prefix. Its
   --  function result, proof input and null dependency would be evaluated by
   --  flow at the label if the label were not also a goto target.

   goto Capture;

   <<Capture>>
   P_Out := Values (Pick (P_Index, Uninitialized))'At (Capture);
end Folded_Inputs;
