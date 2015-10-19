package body Ring_Buffer with SPARK_Mode is
   subtype Index_Range is Integer range 1 .. Max_Size;
   Content : Nat_Array (1 .. Max_Size);
   First   : Index_Range;
   Length  : Length_Range;

   function Valid_Model return Boolean is
     (not Model'Constrained and then
      Length = Model.Length and then
        (for all I in Content'Range =>
             (if I in First .. Integer'Min (First + Length - 1, Max_Size)
              then Content (I) = Model.Content (I - First + 1)
              elsif I in 1 .. First + Length - 1 - Max_Size
              then Content (I) = Model.Content (I + Max_Size - First + 1))));

   function Valid_Model (M : Nat_Array) return Boolean is
     (Length = M'Length and then
      M'First = 1 and then
        (for all I in Content'Range =>
             (if I in First .. Integer'Min (First + Length - 1, Max_Size)
              then Content (I) = M (I - First + 1)
              elsif I in 1 .. First + Length - 1 - Max_Size
              then Content (I) = M (I + Max_Size - First + 1))));

   function Get_Model return Nat_Array is
      L : constant Length_Range := Length;
      R : Nat_Array (1 .. L);
      C : constant Length_Range :=
        Integer'Min (Length, Max_Size + 1 - First);
   begin
      R (1 .. C) :=
        Content (First .. Integer'Min (First + Length - 1, Max_Size));
      R (C + 1 .. Length) := Content (1 .. First + Length - 1 - Max_Size);
      return R;
   end Get_Model;

   procedure Push_Last1 (E : Natural) is
      M : constant Nat_Array := Get_Model with Ghost;
   begin
      if First <= Max_Size - Length then
         Content (First + Length) := E;
      else
         Content (Length - Max_Size + First) := E;
      end if;
      Length := Length + 1;
      pragma Assert (for all I in 1 .. Integer'Min (Length - 1, Max_Size + 1 - First) =>
                       Get_Model (I) = Content (I + First - 1));
      pragma Assert (for all I in Max_Size - First + 2 .. Length - 1 =>
                       Get_Model (I) = Content (I - Max_Size + First - 1));
      pragma Assert (for all I in 1 .. Length - 1 => Get_Model (I) = M (I));
      pragma Assert (Get_Model (Length) = E);
   end Push_Last1;

   procedure Push_Last (E : Natural) is
   begin
      Model := (Model.Length + 1, Model.Content & E);
      if First <= Max_Size - Length then
         Content (First + Length) := E;
      else
         Content (Length - Max_Size + First) := E;
      end if;
      Length := Length + 1;
   end Push_Last;

   procedure Pop_First (E : out Natural) is
   begin
      Model := (Model.Length - 1, Model.Content (2 .. Model.Length));
      E := Content (First);
      Length := Length - 1;
      if First < Max_Size then
         First := First + 1;
      else
         First := 1;
      end if;
   end Pop_First;

   procedure Pop_When_Available (E : in out Natural) is
      procedure Update_Model with Ghost is
      begin
         if Model.Length > 0 then
            Model := (Model.Length - 1, Model.Content (2 .. Model.Length));
         end if;
      end Update_Model;
   begin
      if Length > 0 then
         E := Content (First);
         Length := Length - 1;
         if First < Max_Size then
            First := First + 1;
         else
            First := 1;
         end if;
      end if;
      Update_Model;
   end Pop_When_Available;
end Ring_Buffer;
