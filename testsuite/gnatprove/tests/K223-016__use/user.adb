with Used; use Used;

package body User is
   procedure AbsoluP (x : Integer; res : out Integer) is
   begin
      res := Absolu (x);
   end AbsoluP;
end User;
