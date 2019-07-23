with Mode_Auto; use all type Mode_Auto.T;
package Private_Pointer with SPARK_Mode is
   package Mode_On is
      type T is private;
      function Is_Null (X : T) return Boolean;
      function Get (X : T) return Integer with
        Pre => not Is_Null (X);
      function Uninit_Alloc return T with Volatile_Function,
        Post => not Is_Null (Uninit_Alloc'Result);
      function Init_Alloc (X : Integer) return T with Volatile_Function,
        Post => not Is_Null (Init_Alloc'Result) and Get (Init_Alloc'Result) = X;
      procedure Set (X : T; Y : Integer) with
        Pre => not Is_Null (X),
        Post => Get (X) = Y;
   private
      type My_Int is new Integer with Default_Value => 0;
      type T is access My_Int;
      function Is_Null (X : T) return Boolean is (X = null);
      function Get (X : T) return Integer is (Integer (X.all));
      function Uninit_Alloc return T is
        (new My_Int);
      function Init_Alloc (X : Integer) return T is
        (new My_Int'(My_Int (X)));
   end Mode_On;
   use all type Mode_On.T;

   package Mode_Off is
      type T is private with
        Default_Initial_Condition => Is_Null (T);
      function Is_Null (X : T) return Boolean;
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      function Is_Null (X : T) return Boolean is (X = null);
   end Mode_Off;
   use all type Mode_Off.T;

   X_1 : Mode_On.T;
   pragma Assert (Is_Null (X_1));
   X_2 : Mode_Off.T;
   pragma Assert (Is_Null (X_2));
   X_3 : Mode_Auto.T;
   pragma Assert (Is_Null (X_3));
   pragma Assert (X_3 /= Mode_Auto.C);
   pragma Assert (Mode_Auto.D = X_3);

   X_4 : Mode_On.T := Init_Alloc (5);
   pragma Assert (not Is_Null (X_4));

   procedure Main with Global => (In_Out => X_4);
end Private_Pointer;
