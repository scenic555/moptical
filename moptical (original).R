
# Program moptical - Optimal Item Calibration for Multidimensional Abilities
# Pretesting of M2PL items for achievement tests

# Algorithm from paper:
# Ul Hassan and Miller (2023). Optimal calibration of items for multidimensional 
# achievement tests
#
# Code by Mahmood Ul Hassan and Frank Miller, 2023-12-05 
# Version 1.4.1  (2023-12-05)
#
################################################################################
# Install and load the required packages
################################################################################

#install.packages("mvtnorm")
#install.packages("cubature")
library(mvtnorm)
library(cubature)

################################################################################
# Calculate elements of information matrix at each point of theta*theta for given 
# theta-vector t and k items with parameter values in a and b. Later we use this
# to calculate directional derivatives. 
################################################################################

crit<-function(t,a,b){
  
  k<-length(b) # number of item
  n<-length(t) # number of examinees
  d<-dim(a)[2]
  

  # create t+(t+1)
  smah<-function(x, L=3L) {sapply(1:(length(x)-L+1),function(i){ sum(x[i:(i+L-1)])})}
  x<-y<-c(t[1],(1/2)*smah(t,L=2),t[n]) #length of weight is n+1 
 
  
  fx<-function(x,a,b){1/(1+exp(-(a[1]*x[1]+a[2]*x[2]+b[1])))} #a and b are vector 
  s<-matrix(c(1,0,0,1),2,2)
  #s<-matrix(c(1,0.78,0.78,1),2,2) # change here for var-cov matrix
  dn<-function(x){dmvnorm(x, mean=rep(0,d), sigma=s)}
  
  f11<- function(x,a,b){(fx(x,a,b))*(1-fx(x,a,b))*((x[1])^2)* dn(x)}
  f12<- function(x,a,b){(fx(x,a,b))*(1-fx(x,a,b))*(x[1]*x[2])* dn(x)}
  f13<- function(x,a,b){(fx(x,a,b))*(1-fx(x,a,b))*(x[1])* dn(x)}
  f22<- function(x,a,b){(fx(x,a,b))*(1-fx(x,a,b))*((x[2])^2)* dn(x)}
  f23<- function(x,a,b){(fx(x,a,b))*(1-fx(x,a,b))*(x[2])* dn(x)}
  f33<- function(x,a,b){(fx(x,a,b))*(1-fx(x,a,b))*(1)* dn(x)}
  
  
  M<-array(data=NA, dim=c(3,3,k,n,n)) # save matrix in arry
  
  for(i in 1:k){
  for(m in 1:n){
  for(j in 1:n){
      
      k11<-adaptIntegrate(f11,a[i,],b[i] ,lowerLimit=c(x[j],y[m]), upperLimit=c(x[j+1],y[m+1]))$`integral`
      k12<-adaptIntegrate(f12,a[i,],b[i] ,lowerLimit=c(x[j],y[m]), upperLimit=c(x[j+1],y[m+1]))$`integral`
      k13<-adaptIntegrate(f13,a[i,],b[i] ,lowerLimit=c(x[j],y[m]), upperLimit=c(x[j+1],y[m+1]))$`integral`
      k22<-adaptIntegrate(f22,a[i,],b[i] ,lowerLimit=c(x[j],y[m]), upperLimit=c(x[j+1],y[m+1]))$`integral`
      k23<-adaptIntegrate(f23,a[i,],b[i] ,lowerLimit=c(x[j],y[m]), upperLimit=c(x[j+1],y[m+1]))$`integral`
      k33<-adaptIntegrate(f33,a[i,],b[i] ,lowerLimit=c(x[j],y[m]), upperLimit=c(x[j+1],y[m+1]))$`integral`

      M[,,i,j,m]<-matrix(c(k11,k12,k13,k12,k22,k23,k13,k23,k33),3,3,byrow =T)

    }}}
  M
}

################################################################################
# Function to calculate optimality criteria of multiple designs xii
################################################################################
cret2<-function(M,xii,t,k){
  h<-dim(xii)[1]
  n1<-length(t)
  x2i<-expand.grid(1:n1,1:n1)
  logdetMinv<-c()
  dtt<-c()
  
  for (m in 1:h)
  {
    x2i$it<-xii[m,]
    logdetMinv[m]<- 0
    dtt[m]<-1
    for (i in 1:k)
    {
      id<-subset(x2i,it==i)
      MF<-lapply(1:dim(id)[1],function(s) {M[,,i,id[s,1],id[s,2]]})
      smat<-Reduce("+",MF)
      logdetMinv[m] <-logdetMinv[m]+log(det(solve(smat)))
      dtt[m] <-dtt[m]*det(smat)
    }
  }
  list(logdetMinv=logdetMinv,dtt=dtt)  
}

#################################################################################
# Function to calculate directional derivative for design x2i
#################################################################################
ddriv<-function(M,x2i,a,b,t){
  k<-length(b)
  n<-length(t)
  xi<-x2i$it
  dd <-array(dim=c(k,n*n))
  
  fx<-function(x,a,b){1/(1+exp(-(a[1]*x[1]+a[2]*x[2]+b[1])))}
  x<-expand.grid(t,t)
  
  for (i in 1:k){
    id<-subset(x2i,it==i)
    MF<-lapply(1:dim(id)[1],function(s) {M[,,i,id[s,1],id[s,2]]})
    Minv <-solve(Reduce("+",MF))
    for (j in 1:(n*n)){
    y<-c(x[j,1],x[j,2])
    dd[i,j] <-3- (fx(y,a[i,],b[i]))*(1-fx(y,a[i,],b[i]))*c(-y[1],-y[2],-1) %*% Minv %*% c(-y[1],-y[2],-1)
    }
  }
  list(dd=dd,xi=xi)
}

################################################################################
# Identify worst violation of equivalence theorem
################################################################################
idwv<-function(dd,xi){
  n<-dim(dd)[2]
  ddmin <-array(dim=n)
  ddamin <-array(dim=n)
  vio<-array(dim=n)
  
  for (j in 1:n){
    ddmin[j]  <- min(dd[,j])
    ddamin[j] <- which.min(dd[,j])
    vio[j]    <- dd[xi[j],j] - ddmin[j]
  }
  list(ddmin=ddmin,ddamin=ddamin,vio=vio)
}

################################################################################
# Improve design 
################################################################################
impdesign<-function(viomax,vio,imf,xii,xi,ddamin,dd,t,k){
  li<-length(imf)
  n<-length(xi)
  
  for (m in 1:li){
    for (j in 1:n){ 
      if (vio[j]>(1-imf[m])*viomax)
      { 
        # change sampling to other item
        xii[m,j] <- ddamin[j]
      }
      else { xii[m,j] <- xi[j] }
    }
    # Ensure that each item is sampled
    for (i in 1:k){
      if (sum((xii[m,]==i))==0) 
      {
        j <- which.min(dd[i,2:(n-1)])+1
        print(c("Ensured sampling for ",i," at ",t[i,j]))
        xii[m,j-1] <- i
        xii[m,j]   <- i
        xii[m,j+1] <- i
      }
    }
  }
  list(xii=xii)
}

#################################################################################
# moptical  maximization process

#  t:       ability grid points in one dimension
#  a:       matrix with item discrimination parameters for all items (number of rows determines number of items)
#  b:       Vector of item scale difficulty parameter

#  Hyper parameters for optimization: 
#  imf:     the vector of step-lengths, initially c(0.30,0.35,0.40,0.45)
#  maxiter: maximal number of iterations 
#  eps:     convergence criterion (maximum violation of eq.th.)


# Result of this function is a list with following instances:
#  $dd      directional derivatives of optimal solution
#  $xi      optimal solution
#  $track   A matrix where each row contains information about the iteration 
#           number, violation of equivalence theorem, minimum value of step 
#           length, and the value of step length corresponding to the best design,
#           as well as the maximum value of step length.
#  $ CO     criterion value of optimal design
#  $ CR     criterion value of random design
           
################################################################################

moptical<-function(t,a,b,M,imf,maxiter=1000,eps=0.001){

  n<-length(t)        # number of ability parameter in one direction
  k<-length(b)        # number of item 
  li<-length(imf)     # number of violation proportion used 

  xii<-array(dim=c(li,n*n))     # matrix  li*(n*n)
  track <- array(dim=c(maxiter,6))
  
  x2i<-expand.grid(1:n,1:n)
  xii<-t(replicate(li,sample(1:k, size=n*n, replace=TRUE))) # generate starting design
  
  pp<-cret2(M,xii,t,k) 
  Rald<-pp$logdetMinv  # log(det(M^-1)) of random designs
  Rad<-pp$dtt          # determinant of random designs
  
  iterc<-0;viomax<-100
  while(viomax>eps & iterc<maxiter-1 & imf[li]>0.0001){
    iterc <- iterc +1
  
    hh<-cret2(M,xii,t,k) # calculate the log(det(M^-1)) for given position of item on theta
    logdetMinv<-hh$logdetMinv
    dtt<-hh$dtt
    mm<- which.min(logdetMinv)
    x2i$it<-xii[mm,]
    
    if (iterc>1 && mm==1  && imf[1]>0.00001) imf <- imf/1.08 
    if (iterc>1 && mm==li && imf[li]<0.5)    imf <- imf*1.08
        
    ww<-ddriv(M,x2i,a,b,t) # calculation of direction derivative
    dd<-ww$dd
    xi<-ww$xi
        
    tt<-idwv(dd,xi)
    # identification of violation of equivalence theorem
    ddmin<-tt$ddmin
    ddamin<-tt$ddamin
    vio<-tt$vio
    
    viomax <- max(vio)
    
    track[iterc,1] <- iterc
    track[iterc,2] <- viomax
    track[iterc,3] <- min(logdetMinv)
    track[iterc,4] <- imf[1]    # minimum value of step length
    track[iterc,5] <- imf[mm]   # value of step length correspond to best design 
    track[iterc,6] <- imf[li]   # maximum value of step length
    
    print(c(iterc,viomax,imf[mm]))
        
    idd<-impdesign(viomax,vio,imf,xii,xi,ddamin,dd,t,k) #improve the design 
    xii<-idd$xii
  }
  fuu<-logdetMinv[mm]
  fd<-dtt[mm]
   
  list(dd=dd,xi=xi,track= track,CO=fuu,CR=Rald)
}

################################################################################
# Implementation of algorithm using Example 1
# Other two-dimensional examples can be generated by adjusting a1, a2, and d
# Note: If population's covariance matrix is different (Example 3), this needs
# to be changed in function "crit"
################################################################################
a1 <- c(1,0)
a2 <- c(0,1)
a  <- cbind(a1,a2)
d  <- c(0,0)
t  <- seq(-7,7,length=300)  # 300 ability parameters in one direction between theta=-7 and 7

# compute the partial information matrix at each grid point of theta*theta
# NOTE: The following computation is computationally intensive and can take (depending on 
# the computer power) take e.g. an hour
M<-crit(t,a,d)     


imf<-c(0.3,0.35,0.4,0.45)  # four different step lengths
# NOTE: The following computation is computationally intensive and can take (depending on 
# the computer power) e.g. an hour
yy<-moptical(t,a,d,M,imf,maxiter=1000,eps=0.001)
xi<-yy$xi


# Plot for optimal item calibration
z1<-expand.grid(t,t)
z1$it<-xi
plot(z1[,1],z1[,2],col=z1$it, pch = 15,xlab="Theta-1",ylab="Theta-2")

fuu<-yy$CO          # D-criterion for optimal design
uu<-yy$CR           # D-criterion for random design 
bb<-cbind(a,d)
parm<-length(bb)    # number of parameters 


# Relative efficiency of four random designs compared to optimal design
effi<-(exp(fuu)/exp(uu ))^(1/(parm)) 
effi

# Average (geometric mean) of the four efficiencies
exp(mean(log(effi)))










