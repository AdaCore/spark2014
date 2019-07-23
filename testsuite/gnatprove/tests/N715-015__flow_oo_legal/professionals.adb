with Ada.Text_IO; use Ada.Text_IO;

pragma Warnigns (Off, "assuming * has no effect on global items");
pragma Warnings (Off, "no Global contract available for *");

package body Professionals
  with Refined_State => (State => Skill_Of_The_Day)
is
   Skill_Of_The_Day : Skills;

   subtype Unemployed_Skills is Skills range Nothing .. Nothing;
   subtype Programmer_Skills is Skills range C       .. Python;
   subtype Soldier_Skills    is Skills range Knives  .. Grenades;
   subtype Doctor_Skills     is Skills range Hearts  .. Skin;

   overriding
   function New_Person
     (Name : Unbounded_String;
      DOB  : Integer)
      return Professional
   is (People.New_Person (Name, DOB)
         with Profession              => Unemployed,
              Skilled_In              => Empty_Skill_List,
              Number_Of_People_Killed => 0);

   overriding
   function New_Person (Name : Unbounded_String) return Professional
   is (People.New_Person (Name)
         with Profession              => Unemployed,
              Skilled_In              => Empty_Skill_List,
              Number_Of_People_Killed => 0);

   overriding
   procedure Print (This : Professional) with SPARK_Mode => Off
   is
   begin
      New_Line;
      Put (To_String (Get_Name (This)) & " is ");

      if Is_Alive (This) then
         Put_Line ("alive.");
      else
         Put_Line ("dead.");
      end if;

      Put_Line ("Profession: " & Professions'Image (This.Profession));

      for I in Skill_Range loop
         Put_Line ("Skilled in " & Skills'Image (This.Skilled_In (I)));
         if This.Skilled_In (I) = Nothing then
            exit;
         end if;
      end loop;
   end Print;

   function New_Professional
     (Name : Unbounded_String;
      DOB  : Integer;
      Prof : Professions)
      return Professional
   is
      Tmp : Professional;
   begin
      Person (Tmp)                := New_Person (Name, DOB);
      Tmp.Profession              := Prof;
      Tmp.Skilled_In              := Empty_Skill_List;
      Tmp.Number_Of_People_Killed := 0;

      return Tmp;
   end New_Professional;

   function New_Professional
     (P    : Person;
      Prof : Professions)
      return Professional
   is
      Tmp : Professional;
   begin
      Person (Tmp)                := P;
      Tmp.Profession              := Prof;
      Tmp.Skilled_In              := Empty_Skill_List;
      Tmp.Number_Of_People_Killed := 0;

      return Tmp;
   end New_Professional;

   overriding
   procedure RIP (P : in out Professional) is
   begin
      RIP (Person (P));
   end RIP;

   procedure Set_Training_Of_The_Day (Skill : Skills)
     with Refined_Global => (Output => Skill_Of_The_Day)
   is
   begin
      Skill_Of_The_Day := Skill;
   end Set_Training_Of_The_Day;

   function Has_Licence_To_Kill (P : Professional) return Boolean is
      (P.Profession in Soldier | Doctor);

   function Have_Same_Profession
     (Professional_A, Professional_B : Professional)
      return Boolean
   is (Professional_A.Profession = Professional_B.Profession);

   function Has_Training (P : Professional) return Boolean
     with Refined_Global => Skill_Of_The_Day
   is
   begin
      if not Is_Alive (P) then
         return False;
      end if;

      case P.Profession is
         when Programmer =>
            if Skill_Of_The_Day in Programmer_Skills
              and then (for all S in Skill_Range =>
                          P.Skilled_In (S) /= Skill_Of_The_Day)
            then
               return True;
            else
               return False;
            end if;

         when Soldier =>
            if Skill_Of_The_Day in Soldier_Skills
              and then (for all S in Skill_Range =>
                          P.Skilled_In (S) /= Skill_Of_The_Day)
            then
               return True;
            else
               return False;
            end if;

         when Doctor =>
           if Skill_Of_The_Day in Doctor_Skills
             and then (for all S in Skill_Range =>
                          P.Skilled_In (S) /= Skill_Of_The_Day)
           then
               return True;
           else
               return False;
           end if;

         when Unemployed =>
            return False;
      end case;
   end Has_Training;

   procedure Train (P : in out Professional)
     with Refined_Global => Skill_Of_The_Day
   is
   begin
      for S in Skill_Range loop
         if P.Skilled_In (S) = Nothing then
            P.Skilled_In (S) := Skill_Of_The_Day;
            return;
         end if;
      end loop;
   end Train;

   function Is_Fully_Trained (P : Professional) return Boolean is
   begin
      case P.Profession is
         when Programmer =>
            if (for all S in Programmer_Skills =>
                  (for some I in Skill_Range =>
                     P.Skilled_In (I) = S))
            then
               return True;
            else
               return False;
            end if;

         when Soldier    =>
            if (for all S in Soldier_Skills =>
                  (for some I in Skill_Range =>
                     P.Skilled_In (I) = S))
            then
               return True;
            else
               return False;
            end if;

         when Doctor     =>
            if (for all S in Doctor_Skills =>
                  (for some I in Skill_Range =>
                     P.Skilled_In (I) = S))
            then
               return True;
            else
               return False;
            end if;

         when Unemployed =>
            return False;
      end case;
   end Is_Fully_Trained;

   procedure Another_One_Bites_The_Dust (Killer : in out Professional;
                                         Victim : in out Person'Class)
   is
   begin
      Killer.Number_Of_People_Killed := Killer.Number_Of_People_Killed + 1;
      RIP (Victim);
   end Another_One_Bites_The_Dust;
end Professionals;
