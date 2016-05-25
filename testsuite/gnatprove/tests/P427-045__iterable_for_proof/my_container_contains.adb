package body My_Container_Contains with SPARK_Mode is
   function Mem (C : Container; E : Natural) return Boolean is
     (for some I in C'Range => C (I) = E);

   function Valid (E : Natural) return Boolean is
      (E > 0);

   procedure Modify (C : in out Container) is
   begin
      for I in 1 .. Max loop
         if C (I) = 0 then
            C (I) := 1;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => Valid (C (J)));
      end loop;
   end Modify;

   function First (C : Container) return Cursor is (Cursor'(Index => 1));
   function Next (C : Container; P : Cursor) return Cursor is
     (if P.Index < Max then Cursor'(Index => P.Index + 1)
      else Cursor'(Index => 0));
   function Has_Element (C : Container; P : Cursor) return Boolean is
     (P.Index in 1 .. Max);
   function Element (C : Container; P : Cursor) return Natural is
     (C (P.Index));
end My_Container_Contains;
