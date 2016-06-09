--  TU: 7. Invariant checking is extended to apply to all parts of all tagged
--  inputs and outputs of a subprogram or call. As with globals, this extension
--  applies to all subprograms, not just "boundary" subprograms.

package Type_Invariant_Legal_8 is

   type TT is private;
   type T is tagged private;

   function Pub (X : T) return Integer;
   function E_Pub (X : T) return Integer;

   procedure Pub_In (X : T);
   procedure Pub_Out (X : out T);
   procedure Pub_In_Out (X : in out T);

private
   type TT is new Natural with Type_Invariant => TT /= 0;

   type T is tagged record
      C : TT;
   end record;

   function Priv (X : T) return Integer;
   function E_Priv (X : T) return Integer;

   function E_Pub (X : T) return Integer is (1);  --  @INVARIANT_CHECK:NONE
   function E_Priv (X : T) return Integer is (1);  --  @INVARIANT_CHECK:NONE

end Type_Invariant_Legal_8;
