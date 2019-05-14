with Provider;
package User is
   type T (A : Integer) is private;
   type T_Acc is access T;
private
   type T (A : Integer) is record
      C : Provider.P_Acc;
   end record;
end User;
