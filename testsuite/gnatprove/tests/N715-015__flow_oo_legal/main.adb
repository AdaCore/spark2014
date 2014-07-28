with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with People;                use People;
with Professionals;         use Professionals;


procedure Main is
   Kenny : Person := New_Person (To_Unbounded_String ("Kenneth McCormick"));

   Uni_Student : Professional := New_Professional (Kenny,
                                                   Unemployed);

   ZeroCool    : Professional := New_Professional
     (To_Unbounded_String ("Dade Murphy"),
      01011977,
      Programmer);

   Rambo       : Professional := New_Professional
     (To_Unbounded_String ("John Rambo"),
      06071946,
      Soldier);

   Dr_House    : Professional := New_Professional
     (To_Unbounded_String ("Gregory House"),
      11061959,
      Doctor);

   procedure Train_Everyone is
   begin
      for Skill in Skills loop
         Set_Training_Of_The_Day (Skill);

         if Has_Training (Uni_Student) then
            Train (Uni_Student);
         end if;

         if Has_Training (ZeroCool) then
            Train (ZeroCool);
         end if;

         if Has_Training (Rambo) then
            Train (Rambo);
         end if;

         if Has_Training (Dr_House) then
            Train (Dr_House);
         end if;
      end loop;
   end Train_Everyone;

   procedure OMG is
   begin
      Another_One_Bites_The_Dust (Rambo,
                                  Uni_Student);

      Another_One_Bites_The_Dust (Dr_House,
                                  Kenny);
   end OMG;

   procedure Print_Everyone is
   begin
      Print (Uni_Student);
      Print (ZeroCool);
      Print (Rambo);
      Print (Dr_House);
   end Print_Everyone;

begin
   Train_Everyone;
   OMG;
   Print_Everyone;
end Main;
