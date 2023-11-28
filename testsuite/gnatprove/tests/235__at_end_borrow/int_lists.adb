with Ada.Unchecked_Deallocation;

package body Int_Lists with SPARK_Mode is

   function Model_Impl (L : access constant List) return Sequence is
     (if L = null then Empty_Sequence else Add (Model_Impl (L.N), L.D))
     with Subprogram_Variant => (Structural => L);

   function Model (L : access constant List) return Sequence is
     (Model_Impl (L));

   function Lemma_Model_Def (L : access constant List) return Boolean is (True);

   procedure Set (L : not null access List; D : Integer) is
   begin
      L.D := D;
   end Set;

   procedure Insert (L : in out List_Acc; D : Integer) is
   begin
      L := new List'(D, L);
   end Insert;

   procedure Delete (L : in out List_Acc) is
      procedure Free is new Ada.Unchecked_Deallocation(List, List_Acc);
      To_Free : List_Acc := L;
   begin
      L := To_Free.N;
      Free(To_Free);
   end Delete;

   function Next (L : not null access List) return access List is
   begin
      return L.N;
   end Next;

end Int_Lists;
