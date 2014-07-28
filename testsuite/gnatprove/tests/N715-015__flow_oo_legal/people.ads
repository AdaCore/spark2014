with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package People
  with Abstract_State => Date,
       Initializes    => Date
is
   type Person is tagged private;

   procedure Set_Date (D : Integer)
     with Global => (Output => Date);

   function New_Person
     (Name : Unbounded_String;
      DOB  : Integer)
      return Person;

   function New_Person (Name : Unbounded_String) return Person
     with Global => Date;

   function Get_Name (P : Person) return Unbounded_String;

   procedure Set_Name (P : in out Person; New_Name : Unbounded_String);

   function Get_DOB (P : Person) return Integer;

   procedure Set_DOB (P : in out Person; New_DOB : Integer);

   function Is_Alive (P : Person) return Boolean;

   procedure RIP (P : in out Person);

private

   type Person is tagged record
      Name  : Unbounded_String := To_Unbounded_String ("Nameless");
      DOB   : Integer := -1;
      Alive : Boolean := False;
   end record;

end People;
