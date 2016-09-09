--  TU: 7. Invariant checking is extended to apply to all parts of all tagged
--  inputs and outputs of a subprogram or call. As with globals, this extension
--  applies to all subprograms, not just "boundary" subprograms.

package Type_Invariant_Legal_8 with SPARK_Mode is

   type TT is private;
   type T is tagged private;

   function Pub (X : T) return Integer;  --  @INVARIANT_CHECK:NONE
   function E_Pub (X : T) return Integer;  --  @INVARIANT_CHECK:NONE

   procedure Pub_In (X : T);  --  @INVARIANT_CHECK:NONE
   procedure Pub_Out (X : out T);  --  @INVARIANT_CHECK:PASS
   procedure Pub_In_Out (X : in out T);  --  @INVARIANT_CHECK:PASS

private
   type TT is new Natural with Type_Invariant => TT /= 0; --  @INVARIANT_CHECK:FAIL

   type T is tagged record --  @INVARIANT_CHECK:FAIL
      C : TT;
   end record;

   function Priv (X : T) return Integer;  --  @INVARIANT_CHECK:NONE
   function E_Priv (X : T) return Integer;  --  @INVARIANT_CHECK:NONE

   function E_Pub (X : T) return Integer is (1);
   function E_Priv (X : T) return Integer is (1);

end Type_Invariant_Legal_8;
