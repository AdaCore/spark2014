package Tag_Check is

   type T is tagged record
      X : Integer;
   end record;

   procedure Two (X, Y : T);
   procedure Three (X, Y, Z : T);

   function Make (X : Integer) return T;

   procedure Assign (X : out T'Class; Y : T'Class);

   procedure Make_New (X : out T'Class; Y : Integer);
end Tag_Check;
