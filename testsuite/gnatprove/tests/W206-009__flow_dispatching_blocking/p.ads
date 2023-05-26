package P is
   pragma Elaborate_Body;
   package Q is
      type T is abstract tagged record
         C : Integer;
      end record;

      procedure Process (X : T);
   end Q;

   package R is
      type TT is new Q.T with record
         CC : Integer;
      end record;

      procedure Process (X : TT);
   end R;

   procedure Proxy;

   protected type PT is
      procedure Proc (X : Q.T'Class; Y : Q.T);
   end PT;
end;
