package body People
  with Refined_State => (Date => Today)
is
   Today : Integer;

   procedure Set_Date (D : Integer)
     with Refined_Global => (Output => Today)
   is
   begin
      Today := D;
   end Set_Date;

   function New_Person
     (Name : Unbounded_String;
      DOB  : Integer)
      return Person is
   begin
      return Person'(Name  => Name,
                     DOB   => DOB,
                     Alive => True);
   end New_Person;

   function New_Person (Name : Unbounded_String) return Person
     with Refined_Global => Today
   is
   begin
      return Person'(Name  => Name,
                     DOB   => Today,
                     Alive => True);
   end New_Person;

   function Get_Name (P : Person) return Unbounded_String is (P.Name);

   procedure Set_Name (P : in out Person; New_Name : Unbounded_String) is
   begin
      P.Name := New_Name;
   end Set_Name;

   function Get_DOB (P : Person) return Integer is (P.DOB);

   procedure Set_DOB (P : in out Person; New_DOB : Integer) is
   begin
      P.DOB := New_DOB;
   end Set_DOB;

   function Is_Alive (P : Person) return Boolean is (P.Alive);

   procedure RIP (P : in out Person) is
   begin
      P.Alive := False;
   end RIP;

begin
   Set_Date (23072014);
end People;
