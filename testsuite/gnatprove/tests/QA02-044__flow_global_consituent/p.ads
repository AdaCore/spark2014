package P
  with Abstract_State => State,
       Initializes    => State,
       SPARK_Mode
is
   pragma Elaborate_Body;
private
   X : Boolean := True with Part_Of => State;

   --  Proxies that read X, but with different Global; both OK
   function Proxy1 return Boolean with Global => X;
   function Proxy2 return Boolean with Global => State;

   --  Direct reads of X, with different Globals; both OK
   function F1 return Boolean is (X) with Global => X;
   function F2 return Boolean is (X) with Global => State;

   function F3 return Boolean is (Proxy1) with Global => X;     -- OK
   function F4 return Boolean is (Proxy1) with Global => State; -- OK

   --  Call to Proxy2 whose Global => State introduces Global => State
   function F5 return Boolean is (Proxy2) with Global => X;     -- NOK
   function F6 return Boolean is (Proxy2) with Global => State; -- OK

   function F7 return Boolean is (Proxy1 and Proxy2) with Global => X;    -- NOK
   function F8 return Boolean is (Proxy1 and Proxy2) with Global => State;-- OK

   function F9 return Boolean is (X and Proxy1) with Global => X;    -- OK
   function FA return Boolean is (X and Proxy1) with Global => State;-- OK

   function FB return Boolean is (X and Proxy2) with Global => X;    -- NOK
   function FC return Boolean is (X and Proxy2) with Global => State;-- OK
end;
