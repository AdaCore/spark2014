package body Ring_Buffer with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;
   Content : Nat_Array (1 .. Max_Size);
   First   : Index_Type;
   Length  : Length_Range;

   function Valid_Model return Boolean is
     (Length = Length_Range (My_Seq.Length (Model)) and then
        (for all I in Content'Range =>
             (if I in First .. Integer'Min (First + Length - 1, Max_Size)
              then Content (I) = Get (Model, I - First + 1)
              elsif I in 1 .. First + Length - 1 - Max_Size
              then Content (I) = Get (Model, I + Max_Size - First + 1))));

   function Valid_Model (M : Model_Type) return Boolean is
     (Length = Length_Range (My_Seq.Length (M)) and then
        (for all I in Content'Range =>
             (if I in First .. Integer'Min (First + Length - 1, Max_Size)
              then Content (I) = Get (M, I - First + 1)
              elsif I in 1 .. First + Length - 1 - Max_Size
              then Content (I) = Get (M, I + Max_Size - First + 1))))
   with Refined_Post =>
     (if Valid_Model'Result then
        (for all I in 1 .. Integer'Min (Length, Max_Size - First + 1) =>
              Get (M, I) = Content (I - 1 + First))
      and (for all I in Max_Size - First + 2 .. Length =>
                Get (M, I) = Content (I - Max_Size + First - 1)));

   function Get_Model return Model_Type is
      R : Model_Type;
      C : constant Length_Range :=
        Integer'Min (Length + First - 1, Max_Size);
   begin
      for J in First .. C loop
         pragma Loop_Invariant (Length_Range (My_Seq.Length (R)) = J - First);
         pragma Loop_Invariant
           (for all I in Content'Range =>
             (if I in First .. J - 1
              then Content (I) = Get (R, I - First + 1)));
         R := Add (R, Content (J));
      end loop;

      for J in 1 .. First + Length - 1 - Max_Size loop
         pragma Loop_Invariant (Length_Range (My_Seq.Length (R)) = C - First + J);
         pragma Loop_Invariant
           (for all I in Content'Range =>
              (if I in First .. Integer'Min (First + Length - 1, Max_Size)
               then Content (I) = Get (R, I - First + 1)
               elsif I in 1 .. J - 1
               then Content (I) = Get (R, I + Max_Size - First + 1)));
         R := Add (R, Content (J));
      end loop;
      return R;
   end Get_Model;

   procedure Push_Last1 (E : Natural) is
   begin
      if First <= Max_Size - Length then
         Content (First + Length) := E;
      else
         Content (Length - Max_Size + First) := E;
      end if;
      Length := Length + 1;
   end Push_Last1;

   procedure Push_Last (E : Natural) is
   begin
      Model := Add (Model, E);
      if First <= Max_Size - Length then
         Content (First + Length) := E;
      else
         Content (Length - Max_Size + First) := E;
      end if;
      Length := Length + 1;
   end Push_Last;

   procedure Pop_First (E : out Natural) is
   begin
      Model := Remove (Model, 1);
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
         if My_Seq.Length (Model) > 0 then
            Model := Remove (Model, 1);
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
