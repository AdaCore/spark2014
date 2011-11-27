package P is
   type Dot is record
      X, Y : Integer;
   end record;

   type Color is (Red, Blue, Green);

   type Dots is array (Color) of Dot;

   type Painting is record
      Plain, Shadow : Dots;
   end record;

   --  Example of a contrat over records, arrays, integers and enumerations

   procedure Shadow_Effect (P : in out Painting; D : Dot) with
     Pre  => (for some C in Color => P.Plain(C) = D),
     Post => (for all C in Color =>
                (if P.Plain'Old(C) = D then P.Shadow(C) = D));

   function Get_Plain (P : Painting; C : Color) return Dot is (P.Plain(C));

   function Plain_Is_Dot (P : Painting; C : Color; D : Dot) return Boolean is
      (Get_Plain(P,C) = D);

   function Some_Plain_Is_Dot (P : Painting; D : Dot) return Boolean is
      (for some C in Color => Plain_Is_Dot(P,C,D));

   --  Same contrat with functions abstracting the properties

   procedure Shadow_Effect_2 (P : in out Painting; D : Dot) with
     Pre  => Some_Plain_Is_Dot(P,D),
     Post => (for all C in Color =>
                (if Plain_Is_Dot(P'Old,C,D) then P.Shadow(C) = D));
end P;
