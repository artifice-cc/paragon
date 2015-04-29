
library(ggplot2)
library(reshape2)
library(plyr)
library(stringr)

data.frame.wide <- function(x, vid, vmeasure, long_col)
{
  x$id <- c(1:nrow(x))
  xmelt <- melt(x, c(c("id"), vid, c(long_col)), vmeasure)
  xc <- dcast(xmelt, as.formula(paste(paste(c("id", vid), collapse="+"), "~", long_col)))
  newcols <- as.vector(unique(x[[long_col]]))
  tmpd1 <- data.frame(xc[!is.na(xc[[newcols[1]]]),vid])
  return(cbind(tmpd1, lapply(newcols, function(c) {
    tmpd2 <- data.frame(na.omit(xc[[c]]));
    colnames(tmpd2) <- c(c);
    return(tmpd2);
  })))
}

row.measures.differ <- function(row, dx)
{
  return(any(sapply(6:ncol(dx), function(i) { row[i] != row[5] })))
}

analyze.measure <- function(d, measure, base_strat)
{
  dwide <- data.frame.wide(d, c("Case", "ChanceAnd", "ChanceSplit", "Inconsistent", "Same"),
                           measure, "Strategy")
  #dwide <- cbind(dwide[,1:5], lapply(colnames(dwide)[6:ncol(dwide)], function(col) {
  #  dcol <- data.frame(x=(100.0*(dwide[,col] - dwide[,base_strat] + 1.0)/(dwide[,base_strat] + 1.0)))
  #  colnames(dcol) <- c(paste("REL", col, sep=""))
  #  dcol
  #}))
  #dsub <- dwide[(1:nrow(dwide))[sapply(1:nrow(dwide), function(x) { row.measures.differ(dwide[x,], dwide) })],]
  dsub <- subset(dwide, Same == "false")
  print(paste("nrow dwide:", nrow(dwide), "nrow dsub:", nrow(dsub)))
  dsubm <- melt(dsub, c("Case", "ChanceAnd", "ChanceSplit", "Inconsistent", "Same"))
  print(head(dwide))
  print(head(dsubm))
  print(paste("mean of", base_strat, mean(dwide[,base_strat])))
  #print(lapply(unique(d$Strategy), function(strat) {
  print(lapply(unique(dsubm$variable), function(strat) {
    if(str_sub(strat, 0, 3) != "REL" && strat != base_strat)
    {
      list(strat,
           #paste("pct increase:", mean(dwide[,paste("REL", strat, sep="")])),
           #t.test(d[d$Strategy==strat,measure], d[d$Strategy==base_strat,measure], paired=TRUE))
           t.test(dsubm[dsubm$variable==strat,7], dsubm[dsubm$variable==base_strat,7], paired=TRUE))
    }
  }))
  ggplot(dsubm) + geom_boxplot(aes(x=variable, y=value)) + # , fill=factor(Inconsistent)
    #facet_grid(ChanceAnd ~ ChanceSplit, labeller=label_both) + #labs(fill="Inconsistent") +
    scale_x_discrete("Heuristic") + scale_y_continuous(measure) +
    theme(axis.text.x = element_text(angle = 90, hjust = 1))
}

d <- read.csv("paragon-random-abduce.csv")
#d <- read.csv("paragon-random-contract.csv")
analyze.measure(d, "ExplainedPct", "rand_min-ancestors")
#analyze.measure(d, "ChangePct", "rand_min-ancestors")
#analyze.measure(d, "RecoversPct", "rand")
#analyze.measure(d, "ChangePct", "rand")
#analyze.measure(d, "Microseconds", "rand")

