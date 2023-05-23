package body Iterable_Invariant with SPARK_Mode is

   function First (C : Container) return Cursor is (0);
   function Next (C : Container; X : Cursor) return Cursor is
     (X + 1);
   function Has_Element (C : Container; X : Cursor) return Boolean is (X /= 2);
   function Element (C : Container; X : Cursor) return Boolean is (X /= 0);
   
   procedure Allowed_Quantification (C : Container) is null;
   procedure Forbidden_Quantification (C : Container) is null;

end Iterable_Invariant;
