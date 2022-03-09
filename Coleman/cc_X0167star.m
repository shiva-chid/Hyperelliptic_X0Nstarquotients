SetLogFile("cc_X0167star.log");

load "coleman.m";
// SimplifiedModel(X0NQuotient(176,[16,11]));
Q := y^2 - (x^10 - 8*x^8 + 4*x^7 + 24*x^6 - 16*x^5 - 36*x^4 + 32*x^3 + 16*x^2 - 16*x);
// BadPrimes = 2, 11
p := 3; 
N := 12;
data := coleman_data(Q,p,N);

Qpoints := Q_points(data,1000);

L, v := effective_chabauty(data : Qpoints := Qpoints, e := 40);

printf "L = %o\nQ-points = %o\nv = %o\n", L, Qpoints, v;

if #L eq #Qpoints then
  printf "found all %o Q-points!\n", #Qpoints;
else
  printf "one has to exclude additional %o points\n", #L - #Qpoints;
end if;