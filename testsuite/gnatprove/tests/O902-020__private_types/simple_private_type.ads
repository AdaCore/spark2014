package Simple_Private_Type with SPARK_Mode is
   type My_Int is private;

   O : constant My_Int;

   function Is_Zero (X : My_Int) return Boolean;

   function "=" (X, Y : My_Int) return Boolean with
     Post =>
       "="'Result = ((Is_Zero (X) and Is_Zero (Y))
                     or else P (X) = P (Y));

   function N (X : My_Int) return My_Int with
     Post => not Is_Zero (N'Result) and P (N'Result) = X;

   function P (X : My_Int) return My_Int with
     Pre => not Is_Zero (X);

private
   pragma SPARK_Mode (Off);

   type My_Int (Overflown : Boolean := False) is record
      case Overflown is
         when True => null;
         when False =>
            Content : Integer;
      end case;
   end record;

   O : constant My_Int := (Content => 0, Overflown => False);
end Simple_Private_Type;
