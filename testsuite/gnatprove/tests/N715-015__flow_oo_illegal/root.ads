package Root
  with Abstract_State => State,
       Initializes    => State
is
   procedure Progress_State
     with Global => (In_Out => State);

   type Object_T is tagged record
      X : Integer;
   end record;

   type P_Object_T is tagged private;

   function New_Object return Object_T;

   function New_Object (Input : Integer) return Object_T;

   function New_Object_From_State return Object_T
     with Global => State;

   function New_P_Object return P_Object_T;

   function New_P_Object (Input : Integer) return P_Object_T;

   function New_P_Object_From_State return P_Object_T
     with Global => State;

   procedure New_Object_And_Update_Global_Outputs (O : out Object_T)
     with Global => (In_Out => State);

   procedure Update_Global_Based_On_Object (O : Object_T)
     with Global => (Output => State);

private
   type P_Object_T is tagged record
      Object_X : Object_T;
   end record;

   Default_Object   : constant Object_T   := Object_T'(X => 0);
   Default_P_Object : constant P_Object_T :=
     P_Object_T'(others => Default_Object);

end Root;
