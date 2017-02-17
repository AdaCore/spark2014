with Nobody; use Nobody;

package body Somebody is
   procedure P (X : in out Integer) is
   begin
      X := Divide (X, 2);
   end P;
end Somebody;
