SetLogFile("cc_X0279star.log");

load "coleman.m";
// SimplifiedModel(X0NQuotient(279,[9,31]));
Q := y^2 - (x^12 - 10*x^11 + 47*x^10 - 134*x^9 + 257*x^8 - 346*x^7 + 320*x^6 - 164*x^5 - 10*x^4 + 56*x^3 - 7*x^2 - 2*x + 1);
// BadPrimes = 2, 3, 31
p := 5; 
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