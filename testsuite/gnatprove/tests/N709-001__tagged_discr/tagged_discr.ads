package Tagged_Discr with
  SPARK_Mode
is pragma Elaborate_Body;
   type E is (A, B, C, D);

   type T (Discr : E) is tagged record
      Z : Boolean;
      case Discr is
         when A | C =>
            X : Integer;
         when others =>
            Y : Float;
      end case;
   end record;

   function Is_Zero (V : T) return Boolean is
      (V.Z = False and then
         (case V.Discr is
            when A | C => V.X = 0,
            when others => V.Y = 0.0));

   procedure Init (V : out T) with
     Pre'Class => V.Discr = A,
     Post      => Is_Zero (V);

   procedure Update (V : in out T) with
     Post => Is_Zero (V);

   type U1 is new T with record
      W : Integer;
   end record;

   function Is_Zero (V : U1) return Boolean is
      (V.Z = False and then
         (case V.Discr is
            when A | C => V.X = 0,
            when others => V.Y = 0.0) and then
        V.W = 0);

   procedure Init (V : out U1) with
     Post => Is_Zero (V);

   procedure Update (V : in out U1) with
     Post => Is_Zero (V);

   type U2 is new T with record
      W : Integer;
      XX : Integer;
      YY : Float;
   end record;

   function Is_Zero (V : U2) return Boolean is
      (Is_Zero (T(V)) and then
       V.W = 0 and then
       V.XX = 0 and then
       V.YY = 0.0);

   procedure Init (V : out U2) with
     Post => Is_Zero (V);

   procedure Update (V : in out U2) with
     Post => Is_Zero (V);

end Tagged_Discr;
