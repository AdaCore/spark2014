procedure Effect2 with Global => null is

   E : exception;

   procedure P (X : Boolean) with
     Depends => (null => X),
     Post => not X,
     Exceptional_Cases => (E => X);

   procedure P (X : Boolean) is
   begin
      if X then
         raise E;
      end if;
   end P;

   procedure Call_P (X : Boolean; Y : out Boolean) with
     Depends => (Y => X),
     Post => Y = X;

   procedure Call_P (X : Boolean; Y : out Boolean) is
   begin
      P (X);
      Y := False;
   exception
      when E =>
         Y := True;
   end Call_P;

begin
   null;
end Effect2;
