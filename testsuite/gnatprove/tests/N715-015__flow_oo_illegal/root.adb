package body Root
  with Refined_State => (State => Counter)
is
   Counter : Integer := Integer'First;

   procedure Progress_State
     with Refined_Global => (In_Out => Counter)
   is
   begin
      if Counter < Integer'Last then
         Counter := Counter + 1;
      else
         Counter := Integer'First;
      end if;
   end Progress_State;

   function New_Object return Object_T is (Default_Object);

   function New_Object (Input : Integer) return Object_T is
     (Object_T'(X => Input));

   function New_Object_From_State return Object_T is (Object_T'(X => Counter))
     with Refined_Global => Counter;

   function New_P_Object return P_Object_T is (Default_P_Object);

   function New_P_Object (Input : Integer) return P_Object_T is
     (P_Object_T'(others => Object_T'(X => Input)));

   function New_P_Object_From_State return P_Object_T is
     (P_Object_T'(others => Object_T'(X => Counter)))
     with Refined_Global => Counter;

   procedure New_Object_And_Update_Global_Outputs (O : out Object_T)
     with Refined_Global => (In_Out => Counter)
   is
   begin
      O := New_Object_From_State;
      Progress_State;
   end New_Object_And_Update_Global_Outputs;

   procedure Update_Global_Based_On_Object (O : Object_T)
     with Refined_Global => (Output => Counter)
   is
   begin
      Counter := O.X;
   end Update_Global_Based_On_Object;
end Root;
