package body Store
with
  Refined_State => (State => (Store, Index))
is

   type Index_Type is mod 2 ** 32;
   type Store_Type is array (Index_Type) of Integer;

   Store : Store_Type;
   Index : Index_Type;

   procedure Init
   with
     Refined_Global => (Output => (Store, Index)),
     Refined_Depends => ((Store, Index) => null)
   is
   begin
      Index := 0;
      Store := Store_Type'(others => 0);
   end Init;

   procedure Store_Element (E : Integer)
   with
     Refined_Global => (In_Out => (Store, Index)),
     Refined_Depends =>
       (Index => Index,
        Store =>+ (Index, E))
   is
   begin
      Store (Index) := E;
      Index := Index + 1;
   end Store_Element;

end Store;
