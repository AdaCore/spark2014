with Q;
package P is
   subtype T is Integer range 1 .. Q.F; -- this is equally legal
   --  high bound depends on C, which is known by Entity_Name
end;
