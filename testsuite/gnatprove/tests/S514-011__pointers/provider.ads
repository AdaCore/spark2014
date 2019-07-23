with Original;
package Provider is
   type P_Acc is private;
private
   type P_Acc is access Original.T;
end Provider;
