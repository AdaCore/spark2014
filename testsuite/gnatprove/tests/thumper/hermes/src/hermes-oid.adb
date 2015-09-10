---------------------------------------------------------------------------
-- FILE    : hermes-oid.adb
-- SUBJECT : Body of Object Identifier package.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Hermes.OID is

   ---------------------
   -- Public Subprograms
   ---------------------

   procedure To_Object_Identifier
     (Separates : in  Component_Array;
      Result    : out Object_Identifier;
      Status    : out Status_Type) is

      function Bad_First_Level(Root : Component_Type) return Boolean is
        (not (Root = 0 or Root = 1 or Root = 2));

      function Bad_Second_Level
        (Root : Component_Type; Second : Component_Type) return Boolean is
        (not (case Root is
                 when 0 => Second < 40,
                 when 1 => Second < 40,
                 when 2 => Second <= Second_Level_Component_Type'Last,
                 when others => False));

   begin
      Result := Object_Identifier'(0, 0, Other_Component_Array'(others => 0), 0);
      Status := Success;

      if Separates'Length < 1 or else Bad_First_Level(Separates(Separates'First)) then
         Status := Invalid_Root;
      else
         Result.Root_Component := Separates(Separates'First);
         if Separates'Length < 2 or else
           Bad_Second_Level(Separates(Separates'First), Separates(Separates'First + 1)) then
            Status := Invalid_Second_Level;
         else
            Result.Second_Level_Component := Separates(Separates'First + 1);
            for I in Component_Index_Type range Separates'First + 2 .. Separates'Last loop
               Result.Other_Components(1 + ((I - Separates'First) - 2)) := Separates(I);
            end loop;
            Result.Other_Component_Count := Separates'Length - 2;
         end if;
      end if;
   end To_Object_Identifier;


   function Component_Count(Identifier : Object_Identifier) return Component_Count_Type is
   begin
      return Identifier.Other_Component_Count + 2;
   end Component_Count;


   procedure To_Separates
     (Identifier           : Object_Identifier;
      Result               : out Component_Array;
      Number_Of_Components : out Component_Count_Type) is
   begin
      Result := (others => 0);
      Number_Of_Components := 0;

      if Identifier.Other_Component_Count + 2 <= Result'Length then
         Result(Result'First) := Identifier.Root_Component;
         Result(Result'First + 1) := Identifier.Second_Level_Component;
         for I in Other_Count_Type range 1 .. Identifier.Other_Component_Count loop
            pragma Loop_Invariant(Check =>
               I <= Identifier.Other_Component_Count                 and
               Identifier.Other_Component_Count + 2 <= Result'Length and
               Identifier = Identifier'Loop_Entry);

            Result((Result'First + 2) + (I - 1)) := Identifier.Other_Components(I);
         end loop;
         Number_Of_Components := Identifier.Other_Component_Count + 2;
      end if;
   end To_Separates;


   -- See X.690-2002-07.pdf (bottom of page 13) in the references folder for the specifics about
   -- the encoding. See also http://msdn.microsoft.com/en-us/library/bb540809(v=vs.85).aspx for
   -- a (slightly misleading) graphic.
   --
   procedure To_Octet_Array
     (Identifier  : in  Object_Identifier;
      Result      : out Octet_Array;
      Octet_Count : out Natural) is

      Result_Index : Natural;
      Start_Index  : Natural;
      Left_Index   : Natural;
      Right_Index  : Natural;
      Current_Component : Component_Type;
      Out_Of_Space : Boolean;
      Temp         : Octet;
   begin
      Result := (others => 0);
      Octet_Count := 0;

      if Result'Length > 0 then
         Result_Index := Result'First;
         Octet_Count  := 1;
         Result(Result_Index) :=
           Octet((Identifier.Root_Component * 40) + Identifier.Second_Level_Component);
         for Other_Index in Other_Index_Type range 1 .. Identifier.Other_Component_Count loop
            pragma Loop_Invariant(Result_Index in Result'Range);

            Current_Component := Identifier.Other_Components(Other_Index);

            -- Break the Current_Component value into 7 bit units; store into Result in little
            -- endian order for now.
            Start_Index  := Result_Index;
            Out_Of_Space := False;
            loop
               pragma Loop_Invariant(Result_Index in Result'Range);
               if Result_Index = Result'Last then
                  Out_Of_Space := True;
                  exit;
               else
                  Result_Index := Result_Index + 1;
                  Result(Result_Index) := Octet(Current_Component rem 128);
                  Current_Component := Current_Component / 128;
                  exit when Current_Component = 0;
               end if;
            end loop;

            -- If the loop above broke due to a lack of space, deal with the error condition.
            if not Out_Of_Space then
               -- The proofs fail here because SPARK doesn't know that Result isn't from
               -- Natural'First to Natural'Last. In fact, due to limitations on the number and
               -- size of the OID components, the amount of space used in Result will be far
               -- less. Probably a more suitable type should be defined or at least more
               -- information should be provided in the loop invariants above.
               --
               -- TODO: Fix this failing proof.
               --
               Octet_Count := Result_Index - Start_Index + 1;
            else
               Octet_Count := 0;
               exit;
            end if;

            -- Reverse the order so the 7 bit units are in big endian order instead.
            Left_Index  := Result'First + 1;
            Right_Index := Result_Index;
            while Left_Index < Right_Index loop
               pragma Loop_Invariant(Left_Index in Result'Range and Right_Index in Result'Range);

               Temp                := Result(Left_Index);
               Result(Left_Index)  := Result(Right_Index);
               Result(Right_Index) := Temp;

               Left_Index  := Left_Index + 1;
               Right_Index := Right_Index - 1;
            end loop;

            -- Set MSB of each unit to 1 except for the last one.
            for Index in Natural range Start_Index .. Result_Index - 1 loop
               Result(Index) := Result(Index) + 128;
            end loop;
         end loop;
      end if;
   end To_Octet_Array;

end Hermes.OID;
