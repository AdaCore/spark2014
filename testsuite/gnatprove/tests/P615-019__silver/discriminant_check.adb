procedure Discriminant_Check is

   type Rec (B : Boolean) is record
      case B is
         when True =>
            X : Integer;
         when False =>
            Y : Float;
      end case;
   end record;

   function Get_X (R : Rec) return Integer is
   begin
      return R.X;
   end Get_X;

   procedure Set_X (R : in out Rec; V : Integer) is
   begin
      R.X := V;
   end Set_X;

begin
   null;
end Discriminant_Check;
