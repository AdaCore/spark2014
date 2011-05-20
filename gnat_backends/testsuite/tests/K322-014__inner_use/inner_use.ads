with Pack;
package Inner_Use is
   use Pack;
   X : T;
   procedure P (B : Boolean) with
     Post => X /= 5;
end Inner_Use;

