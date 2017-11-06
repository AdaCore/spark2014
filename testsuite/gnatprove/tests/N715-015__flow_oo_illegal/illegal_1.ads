with Root;

package Illegal_1 is pragma Elaborate_Body;
   G : Integer := 0;

   type Extended_T is new Root.Object_T with record
      Y : Integer;
   end record;

   type P_Extended_T is new Root.P_Object_T with private;

   overriding
   function New_Object return Extended_T;

   overriding
   function New_Object (Input : Integer) return Extended_T;

   overriding
   function New_Object_From_State return Extended_T;

   overriding
   function New_P_Object return P_Extended_T;

   overriding
   function New_P_Object (Input : Integer) return P_Extended_T;

   overriding
   function New_P_Object_From_State return P_Extended_T;

   overriding
   procedure New_Object_And_Update_Global_Outputs (O : out Extended_T);

   overriding
   procedure Update_Global_Based_On_Object (O : Extended_T);

private
   type P_Extended_T is new Root.P_Object_T with record
      Object_Y : Extended_T;
   end record;

end Illegal_1;
