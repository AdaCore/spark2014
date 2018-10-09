with Bad_Ty;
package Use_Bad_Ty with SPARK_Mode is
    T : Integer := Bad_Ty.F;
    pragma assert (T = 1);
end Use_Bad_Ty;
