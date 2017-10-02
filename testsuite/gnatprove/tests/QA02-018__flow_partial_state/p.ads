package P
  with Abstract_State => State,
       Initializes => State,
       SPARK_Mode
is
private
   X : Boolean := True with Part_Of => State;

   function Proxy return Boolean with Global => State;

   function Read1 return Boolean is (Proxy and X) with Global => X;
   function Read2 return Boolean is (Proxy      ) with Global => X;
   function Read3 return Boolean is (          X) with Global => X;

   function Read4 return Boolean is (Proxy and X) with Global => State;
   function Read5 return Boolean is (Proxy      ) with Global => State;
   function Read6 return Boolean is (          X) with Global => State;
end;
