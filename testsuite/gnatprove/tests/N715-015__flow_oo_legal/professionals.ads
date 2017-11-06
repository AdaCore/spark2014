with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with People;                use People;
with Printable;

pragma Warnigns (Off, "assuming * has no effect on global items");
pragma Warnings (Off, "no Global contract available for *");

package Professionals
  with Abstract_State => State
is pragma Elaborate_Body;
   type Professions is (Unemployed,
                        Programmer,
                        Soldier,
                        Doctor);

   type Skills is (Nothing,
                   C, Ada, Java, Python,
                   Knives, Guns, Rifles, Grenades,
                   Hearts, Brains, Limbs, Skin);

   type Professional is new Person and Printable.Object with private;

   overriding
   function New_Person
     (Name : Unbounded_String;
      DOB  : Integer)
      return Professional;

   overriding
   function New_Person (Name : Unbounded_String) return Professional;

   overriding
   procedure Print (This : Professional);

   function New_Professional
     (Name : Unbounded_String;
      DOB  : Integer;
      Prof : Professions)
      return Professional;

   function New_Professional
     (P    : Person;
      Prof : Professions)
      return Professional;

   overriding
   procedure RIP (P : in out Professional);

   procedure Set_Training_Of_The_Day (Skill : Skills)
     with Global => (Output => State);

   function Has_Licence_To_Kill (P : Professional) return Boolean;

   function Have_Same_Profession
     (Professional_A, Professional_B : Professional)
      return Boolean;

   function Has_Training (P : Professional) return Boolean
     with Global => State;

   procedure Train (P : in out Professional)
     with Pre'Class => Has_Training (P),
          Global => State;

   function Is_Fully_Trained (P : Professional) return Boolean;

   procedure Another_One_Bites_The_Dust (Killer : in out Professional;
                                         Victim : in out Person'Class)
     with Pre'Class => Is_Alive (Killer)
                  and then Is_Alive (Victim)
                  and then Has_Licence_To_Kill (Killer),
          Post'Class => Is_Alive (Killer)
                  and then not Victim.Is_Alive;

private
   type Skill_Range is range 1 .. 4;
   type Skill_List is array (Skill_Range) of Skills;

   Empty_Skill_List : constant Skill_List := Skill_List'(others => Nothing);

   type Professional is new Person and Printable.Object with record
      Profession              : Professions;
      Skilled_In              : Skill_List;
      Number_Of_People_Killed : Natural;
   end record;

end Professionals;
