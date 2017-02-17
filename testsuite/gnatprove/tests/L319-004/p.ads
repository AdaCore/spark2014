generic
   type T is private;
package P is
   Default : Boolean := True;
   function F (X : T; Y : Boolean := Default) return T;
   function F (X, Y : T; Z : Boolean := Default) return T;
   procedure Proc (X : in out T);
end P;
