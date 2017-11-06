package Objects with
  SPARK_Mode
is pragma Elaborate_Body;
   type Init_Phase is
     (Not_Started, Database_In_Place, Object_Pool_In_Place, Ended);

   Current_Init_Phase : Init_Phase := Not_Started;

   type Drawable is interface;

   function At_Origin (X : Drawable) return Boolean is abstract;

   procedure Initialize (X : out Drawable) is abstract with
     Pre'Class  => Current_Init_Phase >= Database_In_Place,
     Post'Class => X.At_Origin;

   type Composable is interface;

   function Num_Sub_Objects (X : Composable) return Natural is abstract;

   procedure Initialize (X : out Composable) is abstract with
     -- Pre'Class  => True implicitly
     Post'Class => X.Num_Sub_Objects = 0;

   type Object is new Drawable and Composable with record
      Position_X  : Integer;
      Position_Y  : Integer;
      Num_Subs    : Natural;
   end record;

   overriding
   function At_Origin (X : Object) return Boolean is
      (X.Position_X = 0 and X.Position_Y = 0);

   overriding
   function Num_Sub_Objects (X : Object) return Natural is
      (X.Num_Subs);

   procedure Initialize (X : out Object) with
     Pre'Class  => Current_Init_Phase >= Object_Pool_In_Place,
     Post'Class => X.At_Origin and X.Num_Sub_Objects = 0;

end Objects;
