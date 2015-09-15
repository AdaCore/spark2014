with C.B;

package body C with
   SPARK_Mode,
   Refined_State => (State =>  (C.B.X, C.B.Y))
is
   procedure Read (Value :    out Integer)
   --  Bug is that we do not strip out C.B.Y from the generated refinement.
   --  Overall, we should produce this refined depends:
   --     Refined_Depends => ((Value, C.B.X) => C.B.X)
   --  But instead we include C.B.Y.
   is
   begin
      Value := B.X;
   end Read;

   procedure Is_Positive (Result :    out Boolean) is
      Value : Integer;
   begin
      Read (Value);
      Result := Value > 0;
   end Is_Positive;
end C;
