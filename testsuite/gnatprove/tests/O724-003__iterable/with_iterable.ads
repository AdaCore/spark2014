package With_Iterable with SPARK_Mode is
   Max : constant Natural := 100;
   type My_Array is array (1 .. Max) of Natural;
   type Container is record
      Content : My_Array;
   end record with
     Iterable => (First       => First,
                  Has_Element => Has_Element,
                  Next        => Next);
   type Cursor (C : Natural) is record
      I : Natural;
   end record;
--       with Dynamic_Predicate => Cursor.I in 1 .. Cursor.C;
   subtype Cursor_2 is Cursor (Max + 1);

   function Get (A : Container; I : Natural) return Natural is
     (A.Content (I))
   with
     Pre => I in 1 .. 100;
--
   function First (A : Container) return Cursor_2 is
     ((C => Max + 1, I => 1));
   function Next (A : Container; Cu : Cursor_2) return Cursor_2 is
     (Cu'Update(I => Cu.I + 1))
   with Pre => Has_Element (A, Cu);
   function Has_Element (A : Container; Cu : Cursor_2) return Boolean is
     (Cu.I in 1 .. 100);

   function Contains_0 (A : Container) return Boolean is
     (for some Cu in A => Get (A, Cu.I) = 0);

   procedure Set_To_0 (A : in out Container) with
   Post => Contains_0 (A);
end With_Iterable;
